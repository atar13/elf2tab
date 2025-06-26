//! Convert ELF to TBF.

use crate::header;
use crate::util::{self, align_to, amount_alignment_needed};
use elf::abi::{DT_NEEDED, DT_STRTAB, STB_GLOBAL, STT_FUNC};
use elf::to_str::{e_type_to_human_str, e_type_to_string};
use ring::signature::KeyPair;
use ring::{rand, signature};
use sha2::{Digest, Sha256, Sha384, Sha512};
use std::cmp;
use std::collections::HashMap;
use std::io::{Read, Seek, SeekFrom, Write};
use std::mem;
use std::path::{Path, PathBuf};
use std::{fs, io};
use std::fmt::Write as fmtwrite;

/// Helper function for reading RSA DER key files.
fn read_rsa_file(path: &std::path::Path) -> Result<Vec<u8>, std::io::Error> {
    let mut file = std::fs::File::open(path)?;
    let mut contents: Vec<u8> = Vec::new();
    file.read_to_end(&mut contents)?;
    Ok(contents)
}

/// Helper function to determine if any nonzero length section is inside a
/// given segment.
///
/// This is necessary because we sometimes run into loadable segments that
/// shouldn't really exist (they are at addresses outside of what was
/// specified in the linker script), and we want to be able to skip them.
fn section_exists_in_segment(
    shdrs: &[(String, elf::section::SectionHeader)],
    segment: &elf::segment::ProgramHeader,
) -> bool {
    for (_, shdr) in shdrs.iter() {
        if shdr.sh_size > 0 && section_in_segment(shdr, segment) {
            return true;
        }
    }
    false
}

/// Helper function to determine if a section is within a specific segment.
///
/// Based on the function `section_in_segment` in
/// https://github.com/eliben/pyelftools
fn section_in_segment(
    section: &elf::section::SectionHeader,
    segment: &elf::segment::ProgramHeader,
) -> bool {
    let segtype = segment.p_type;
    let sectype = section.sh_type;
    let secflags = section.sh_flags as u32;

    // Only PT_LOAD, PT_GNU_RELRO and PT_TLS segments can contain SHF_TLS
    // sections.
    if (secflags & elf::abi::SHF_TLS > 0)
        && (segtype == elf::abi::PT_TLS
            || segtype == elf::abi::PT_GNU_RELRO
            || segtype == elf::abi::PT_LOAD)
    {
        // OK
    } else if (secflags & elf::abi::SHF_TLS == 0)
        && !(segtype == elf::abi::PT_TLS || segtype == elf::abi::PT_GNU_RELRO)
    {
        // OK
    } else {
        return false;
    }

    // PT_LOAD and similar segments only have SHF_ALLOC sections.
    if (secflags & elf::abi::SHF_ALLOC == 0)
        && (segtype == elf::abi::PT_LOAD
            || segtype == elf::abi::PT_DYNAMIC
            || segtype == elf::abi::PT_GNU_EH_FRAME
            || segtype == elf::abi::PT_GNU_RELRO
            || segtype == elf::abi::PT_GNU_STACK)
    {
        return false;
    }

    // In ELF_SECTION_IN_SEGMENT_STRICT the flag check_vma is on, so if this
    // is an alloc section, check whether its VMA is in bounds.
    if secflags & elf::abi::SHF_ALLOC > 0 {
        let secaddr = section.sh_addr;
        let vaddr = segment.p_vaddr;

        // This checks that the section is wholly contained in the segment.
        // The third condition is the 'strict' one - an empty section will
        // not match at the very end of the segment (unless the segment is
        // also zero size, which is handled by the second condition).
        if !(secaddr >= vaddr
            && secaddr - vaddr + section.sh_size <= segment.p_memsz
            && secaddr - vaddr <= segment.p_memsz - 1)
        {
            return false;
        }
    }

    // If we've come this far and it's a NOBITS section, it's in the
    // segment.
    if sectype == elf::abi::SHT_NOBITS {
        return true;
    }

    let secoffset = section.sh_offset;
    let poffset = segment.p_offset;

    // Same logic as with secaddr vs. vaddr checks above, just on offsets in
    // the file.
    secoffset >= poffset
        && secoffset - poffset + section.sh_size <= segment.p_filesz
        && secoffset - poffset <= segment.p_filesz - 1
}

#[derive(Debug)]
pub struct AppFuncReloc {
    /// Name of function to relocate
    fn_name: String,
    /// Address of GOT entry for function
    /// within the app's flash 
    app_got_addr: u32,
}

/// Shared library relocation information
struct ShLibFnReloc {
    /// Name of library which contains the 
    /// function code.
    /// To be populated when elf2tab searches through
    /// function symbols in libraries passed in and finds
    /// which one has the needed function symbol.
    lib_name: String,
    /// Offset of function in shared library flash
    lib_fn_offset: u32,
}

/// Helper function to get the names of any shared library 
/// dependencies that this ELF depends on.
///
/// The library names include their file extension (such as .so).
fn get_shared_library_deps(elf_file: &elf::ElfBytes::<elf::endian::AnyEndian>, elf_file_buf: &[u8]) -> Result<Vec<String>, ()> {
    // Loop through structures in .dynamic section
    if let Ok(Some(parsing_table)) = elf_file.dynamic() {
        let mut shlib_strtab_idxs= Vec::new();
        let mut strtab_addr = None;
        for dynamic_structure in parsing_table.iter() {
            match dynamic_structure.d_tag {
                DT_NEEDED => {
                    // From page 80 of https://refspecs.linuxfoundation.org/elf/elf.pdf
                    // This element holds the string table offset of a null-terminated string, giving
                    // the name of a needed library. The offset is an index into the table recorded
                    // in the DT_STRTAB entry. See "Shared Object Dependencies'' for more
                    // information about these names. The dynamic array may contain multiple
                    // entries with this type. These entries' relative order is significant, though
                    // their relation to entries of other types is not.
                    shlib_strtab_idxs.push(dynamic_structure.d_val() as usize);
                },
                DT_STRTAB => {
                    // Gets the address of our strtab (string table) 
                    // See Chapter 1 of https://refspecs.linuxfoundation.org/elf/elf.pdf
                    //
                    // However, this address is in flash and is of the format 0x8_______.
                    // So, to use this address to index into the ELF file, we AND it with 0x0FFFFFFF.
                    // The OR with 0x1000 is because for some reason the strtab started at
                    // an offset of 0x1000 away from the given address.
                    let fixed_strtab_addr = (dynamic_structure.d_ptr() & 0x0FFFFFFF) | 0x1000;
                    strtab_addr = Some(fixed_strtab_addr as usize);
                }
                _ => () 
            }
        };
        strtab_addr.map_or(Err(()), |strtab_addr| {
            let b = &elf_file_buf.iter().as_slice()[strtab_addr..];
            let new_strtab = elf::string_table::StringTable::new(b);
            let mut dep_names = Vec::new();
            for idx in shlib_strtab_idxs {
                let _ = new_strtab.get(idx).map(|dep_name| {
                    dep_names.push(dep_name.to_string())
                });
            }
            Ok(dep_names)
        })
    } else {
        Err(())
    }
}

/// Should output a list of each function that needs relocation and
/// where the address needs to be fixed up.
/// 
/// Then, Tockloader can take this information and fixup the 
/// app binary to have the correct address where the library
/// function is in flash.
fn get_fn_relocs(verbose: bool, elf_sections: &Vec<(String, elf::section::SectionHeader)>, app_elf_file: &elf::ElfBytes::<elf::endian::AnyEndian>, app_elf_file_buf: &[u8], got_start_address_in_tbf: usize) -> Result<Vec<AppFuncReloc>, ()> {
    let fn_names = if let Ok(Some((dyn_symtab, dyn_sym_strtab))) = app_elf_file.dynamic_symbol_table() {
        let mut fn_names = vec![];
        for sym in dyn_symtab {
            let sym_type = sym.st_symtype();
            let bind_type = sym.st_bind();
            if sym_type == STT_FUNC && bind_type == STB_GLOBAL {
                let fn_name = dyn_sym_strtab.get(sym.st_name as usize).unwrap();
                // println!("function name {} {} {}", fn_name, sym.st_value, sym.st_shndx);
                fn_names.push(fn_name);
            }
        }
        fn_names
    } else {
        vec![]
    };
    let rel_data = elf_sections
        .iter()
        .find(|(sh_name, _)| *sh_name == ".rel.text")
        .map(|(_, shdr)| {
            app_elf_file.section_data_as_rels(shdr)
        });


    let (symtab, strtab) = app_elf_file.symbol_table().unwrap().unwrap();

    let mut relocs: Vec<AppFuncReloc> = vec![];
    if let Some(Ok(rels)) = rel_data {
        for rel in rels.into_iter() {
            let symtab_entry = symtab.get(rel.r_sym as usize).unwrap();
            let sym_name = strtab.get(symtab_entry.st_name as usize).unwrap();
            for fn_name in &fn_names {
                if *fn_name == sym_name {
                    if verbose {
                        println!("found matching symbol for function needed to be relocated: {}", sym_name);
                        println!("\t{:08X}", rel.r_offset);
                        println!("\t{} {}", symtab_entry.st_value, symtab_entry.st_shndx);
                    }

                    let (_, shdr) = elf_sections
                        .iter()
                        .find(|(sh_name, _)| *sh_name == ".text")
                        .map(|(_, shdr)| {
                            (app_elf_file.section_data(shdr).unwrap(), shdr)
                        }).unwrap();

                    if verbose {
                        println!("shdr .text offset {:08X}, addr {:08X}", shdr.sh_offset, shdr.sh_addr);
                    }

                    let addr_in_file = ((rel.r_offset - shdr.sh_addr) + shdr.sh_offset) as usize;
                    let got_offset = &app_elf_file_buf[addr_in_file..addr_in_file+4];
                    let mut got_offset_bytes = [0; 4];
                    got_offset_bytes.copy_from_slice(&got_offset[0..4]);
                    let got_offset_addr = u32::from_le_bytes(got_offset_bytes);
                    
                    let got_shdr = elf_sections
                        .iter()
                        .find(|(sh_name, _)| *sh_name == ".got")
                        .map(|(_, shdr)| {
                            shdr
                        }).unwrap();

                    if verbose {
                        println!("GOT is at {:08X} in ELF file", got_shdr.sh_offset);
                        println!("GOT is at {:08X} in TBF file", got_start_address_in_tbf);
                    }

                    let fn_got_entry = got_start_address_in_tbf as u32 + got_offset_addr;
                    if verbose {
                        println!("{} entry in GOT is at {:08X} in file", fn_name, fn_got_entry);
                    }
                    relocs.push(AppFuncReloc{
                        fn_name: (*fn_name).to_string(),
                        app_got_addr: fn_got_entry
                    });
                }
            }
        };
    };

    Ok(relocs)

    // DOESN'T WORK WITH FUNCTION POINTERS
    // // Loop through structures in .dynamic section
    // if let Ok(Some(parsing_table)) = app_elf_file.dynamic() {
    //     let mut jmp_rel_addr = None;
    //     let mut plt_rel_size = None;
    //     let mut rel_entry_size = None;
    //
    //     for dynamic_structure in parsing_table.iter() {
    //         match dynamic_structure.d_tag {
    //             DT_JMPREL => {
    //                 jmp_rel_addr = Some(((dynamic_structure.d_ptr() & 0x0FFFFFFF) | 0x1000) as usize);
    //             },
    //             DT_PLTRELSZ => {
    //                 plt_rel_size = Some(dynamic_structure.d_val() as usize);
    //             },
    //             DT_PLTREL => {
    //                 if dynamic_structure.d_val() != DT_REL as u64 {
    //                     return Err(())
    //                 }
    //             },
    //             DT_RELENT => {
    //                 rel_entry_size = Some(dynamic_structure.d_val() as usize);
    //             },
    //             _ => () 
    //         }
    //     };
    //     
    //     // println!("Relocation info: DT_JMP_REL: {:X?}, DT_PLTRELSZ: {:?}, DT_RELENT: {:?}", jmp_rel_addr, plt_rel_size, rel_entry_size);
    //
    //     jmp_rel_addr.map_or(Err(()), |jmp_rel_addr| {
    //         plt_rel_size.map_or(Err(()), |plt_rel_size| {
    //             let mut fn_relocs: Vec<AppFuncReloc> = Vec::new();
    //
    //             let jmp_rel_end_addr = jmp_rel_addr + plt_rel_size;
    //
    //             // Parse relocation table entries (only those relating to jumps)
    //             // See page 1-22 of https://refspecs.linuxfoundation.org/elf/elf.pdf
    //             const R_OFFSET_LEN: usize = 4;
    //             const R_INFO_LEN: usize = 4;
    //             for addr in (jmp_rel_addr..jmp_rel_end_addr).step_by(R_OFFSET_LEN + R_INFO_LEN) {
    //
    //                 let r_offset_end = addr + R_OFFSET_LEN;
    //
    //                 let mut r_offset_le_bytes: [u8; R_OFFSET_LEN] = [0; R_OFFSET_LEN];
    //                 r_offset_le_bytes.copy_from_slice(&app_elf_file_buf[addr..r_offset_end]);
    //                 let r_offset = u32::from_le_bytes(r_offset_le_bytes);
    //
    //                 let mut r_info_le_bytes: [u8; R_INFO_LEN] = [0; R_INFO_LEN];
    //                 r_info_le_bytes.copy_from_slice(&app_elf_file_buf[r_offset_end..(r_offset_end + R_INFO_LEN)]);
    //                 let r_info = u32::from_le_bytes(r_info_le_bytes);
    //
    //                 // See page 1-22 of https://refspecs.linuxfoundation.org/elf/elf.pdf
    //                 // #define ELF32_R_SYM(i) ((i)>>8)
    //                 let r_symtab_idx = r_info >> 8;
    //                 
    //                 // println!("0x{:x}: r_offset {:x}, r_info {:x}", addr, r_offset, r_info);
    //                 // println!("r_symtab_idx {:x}", r_symtab_idx);
    //                 if let Ok(Some((symtab, sym_strtab))) = app_elf_file.dynamic_symbol_table() {
    //                     if let Ok(symbol) = symtab.get(r_symtab_idx as usize) {
    //                         // println!("{:?}", symbol);
    //                         let fn_name = sym_strtab.get(symbol.st_name as usize);
    //                         // println!("r_sym {:?}", fn_name);
    //                         if let Ok(fn_name) = fn_name {
    //                             fn_relocs.push(AppFuncReloc { fn_name: fn_name.to_string(), app_got_addr: r_offset })
    //                         }
    //                     };
    //                 };
    //             }
    //             Ok(fn_relocs)
    //         })
    //     })
    // } else {
    //     Err(())
    // }
}

/// Helper function to find a function symbol in a shared library ELF file.
fn find_fn_in_shlib(verbose: bool, shlib_elf_file: &elf::ElfBytes::<elf::endian::AnyEndian>, fn_name: &String) -> Option<u32> {
    if let Ok(Some((symtab, sym_strtab))) = shlib_elf_file.symbol_table() {
        if let Some(fn_symbol) = symtab.iter().find(|sym| {
            let name = sym_strtab
                .get(sym.st_name as usize)
                .expect("Failed to parse symbol name");
            name == fn_name 
        }) {
            if verbose {
                println!("Found fn {} at address 0x{:08X}", fn_name, fn_symbol.st_value);
            }
            return Some(fn_symbol.st_value as u32);
        };
    };
    None
}

/// Output relocation information to a TOML formatted string.
fn output_relocation_file (verbose: bool, shlib_deps: Option<Vec<PathBuf>>, app_relocs: Vec<AppFuncReloc>, package_name: &String, output_relocation: &mut String) -> io::Result<()> {
    if verbose {
        println!("APP RELOCS {:?}", app_relocs);
        for reloc in &app_relocs {
            println!("App needs relocation of function {} which has GOT address of 0x{:X}", reloc.fn_name, reloc.app_got_addr);
        }
    }
    if let Some(shlib_deps) = &shlib_deps {
        let mut shlib_fn_relocs: HashMap<String, ShLibFnReloc> = HashMap::new();

        for shlib in shlib_deps {
            if verbose {
                println!("Found shared library dependency at: {}", shlib.display())
            }
            let mut shlib_file = fs::File::open(shlib).expect("Could not open the shared library elf file.");
            let mut shlib_elf_file_buf = Vec::<u8>::default();
            shlib_file.read_to_end(&mut shlib_elf_file_buf)?;
            let shlib_elf_file = elf::ElfBytes::<elf::endian::AnyEndian>::minimal_parse(shlib_elf_file_buf.as_slice())
                .expect("Could not parse the shared library elf file.");

            let shlib_name = shlib.as_path().file_stem().expect("Could not get shared library filename").to_string_lossy().to_string();

            // For each function we need to relocate, 
            // find it in the shared libraries we were given
            for reloc in &app_relocs {
                // if we already found this function in another shared library, skip it
                if shlib_fn_relocs.contains_key(&reloc.fn_name) {
                    continue;
                }

                if verbose {
                    println!("Searching for fn {} in shared library {}", &reloc.fn_name, shlib_name);
                }

                let fn_offset = find_fn_in_shlib(verbose, &shlib_elf_file, &reloc.fn_name);
                if let Some(fn_offset) = fn_offset {
                    let shlib_reloc = ShLibFnReloc { 
                        lib_name: shlib_name.clone(), 
                        lib_fn_offset: fn_offset 
                    };
                    shlib_fn_relocs.insert(reloc.fn_name.clone(), shlib_reloc);
                }
            }
        }

        // Create a relocation TOML file that will look something like this:
        // [ml_func]
        // app_got_addr = 0x000
        // lib_name = "libtest.so"
        // lib_func_offset = 0x00
        //
        // It will help tockloader update GOT entries needed for 
        // function calls into shared libraries 
        for reloc in &app_relocs {
            if let Some(shlib_fn_reloc) = shlib_fn_relocs.get(&reloc.fn_name) {
                writeln!(output_relocation, "[{}]", reloc.fn_name).unwrap();
                writeln!(output_relocation, "app_name = \"{}\"", package_name).unwrap();
                writeln!(output_relocation, "app_got_addr = 0x{:x}", reloc.app_got_addr).unwrap();
                writeln!(output_relocation, "lib_name = \"{}\"", shlib_fn_reloc.lib_name).unwrap();
                writeln!(output_relocation, "lib_func_offset = 0x{:x}", shlib_fn_reloc.lib_fn_offset).unwrap();
            };
        }

        if verbose {
            println!("Generating relocation TOML for function relocations:");
            println!("{}", output_relocation);
        }
    }
    Ok(())
}

/// Convert an ELF file to a TBF (Tock Binary Format) binary file.
///
/// This will place all segments from the ELF file into a binary and prepend a
/// TBF header to it. For all writeable sections in the included segments, if
/// there is a .rel.X section it will be included at the end with a 32 bit
/// length parameter first.
///
/// Assumptions:
/// - Any segments that are writable and set to be loaded into flash but with a
///   different virtual address will be in RAM and should count towards minimum
///   required RAM.
/// - Sections that are writeable flash regions include .wfr in their name.
pub fn elf_to_tbf(
    input_file: &mut fs::File,
    output: &mut Vec<u8>,
    package_name: Option<String>,
    verbose: bool,
    stack_len: Option<u32>,
    app_heap_len: u32,
    kernel_heap_len: u32,
    protected_region_size_arg: Option<u32>,
    permissions: Vec<(u32, u32)>,
    storage_ids: (Option<u32>, Option<Vec<u32>>, Option<Vec<u32>>),
    kernel_version: Option<(u16, u16)>,
    short_id: Option<u32>,
    disabled: bool,
    minimum_footer_size: u32,
    app_version: u32,
    sha256: bool,
    sha384: bool,
    sha512: bool,
    rsa4096_private_key: Option<PathBuf>,
    shlib_deps: Option<Vec<PathBuf>>,
    output_relocation: &mut String,
) -> io::Result<()> {
    let package_name = package_name.unwrap_or_default();

    // Load and parse ELF.
    let mut elf_file_buf = Vec::<u8>::default();
    input_file.read_to_end(&mut elf_file_buf)?;
    let elf_file = elf::ElfBytes::<elf::endian::AnyEndian>::minimal_parse(elf_file_buf.as_slice())
        .expect("Could not parse the .elf file.");

    let (shdr_tab, strtab) = match elf_file.section_headers_with_strtab() {
        Ok((Some(shdr_tab), Some(strtab))) => (shdr_tab, strtab),
        _ => {
            // We use the section headers to find sections like .symtab, .stack, and *.wfr
            panic!("Cannot convert ELF file with no section headers");
        }
    };

    let elf_type = elf_file.ehdr.e_type;

    if verbose {
        println!("Parsing ELF of type {} ({})", e_type_to_string(elf_type), e_type_to_human_str(elf_type).unwrap());
    }

    let elf_sections: Vec<(String, elf::section::SectionHeader)> = shdr_tab
        .iter()
        .map(|shdr| {
            (
                strtab
                    .get(shdr.sh_name as usize)
                    .expect("Failed to parse section name")
                    .to_string(),
                shdr,
            )
        })
        .collect();

    let (is_shared_library, deps) = match elf_type {
        elf::abi::ET_DYN => 
            // is a shared library
            (1, None),
        _ => {
            // is not a shared library, find which ones we depend on
            (0, get_shared_library_deps(&elf_file, &elf_file_buf).ok())
        }
    };

    if verbose {
        let _ = deps.map(|deps| {
            println!("Depends on shared libraries: {:?}", deps);
        });
    }

    let mut shlib_dep_names: Vec<String> = Vec::new();
    if let Some(shlib_deps) = &shlib_deps {
        for shlib in shlib_deps {
            if verbose {
                println!("Found shared library dependency at: {}", shlib.display())
            }
            let mut shlib_file = fs::File::open(shlib).expect("Could not open the shared library elf file.");
            let mut shlib_elf_file_buf = Vec::<u8>::default();
            shlib_file.read_to_end(&mut shlib_elf_file_buf)?;

            let shlib_name = shlib.as_path().file_stem().expect("Could not get shared library filename").to_string_lossy().to_string();
            shlib_dep_names.push(shlib_name.clone());
        }
    }

    let mut elf_phdrs: Vec<elf::segment::ProgramHeader> = elf_file
        .segments()
        .expect("Failed to locate ELF program headers")
        .iter()
        .collect();

    /// Specify how elf2tab should add trailing padding to the end of the TBF
    /// file.
    enum TrailingPadding {
        /// Make sure the entire TBF is a power of 2 in size, so add any
        /// necessary padding to make that happen.
        TotalSizePowerOfTwo,
        /// Make sure the entire TBF is a multiple of a specific value.
        TotalSizeMultiple(usize),
    }

    // Add trailing padding for certain architectures.
    //
    // - ARM: make sure the entire TBF is a power of 2 to make configuring the
    //   MPU easy.
    // - RISC_V: make sure the entire TBF is a multiple of 4 to meet TBF
    //   alignment requirements.
    // - x86: use 4k padding to match page size.
    let trailing_padding = match elf_file.ehdr.e_machine {
        elf::abi::EM_ARM => Some(TrailingPadding::TotalSizePowerOfTwo),
        elf::abi::EM_RISCV => Some(TrailingPadding::TotalSizeMultiple(4)),
        elf::abi::EM_386 => Some(TrailingPadding::TotalSizeMultiple(4096)),
        _ => None,
    };

    ////////////////////////////////////////////////////////////////////////////
    // Determine the amount of RAM this app needs.
    ////////////////////////////////////////////////////////////////////////////

    // Set the size of the stack, either as specified by command line arguments,
    // based on a section set by the linker, or if all else fails to a default
    // value.
    let stack_len = stack_len
        // not provided, read from binary
        .or_else(|| {
            elf_sections.iter().find_map(|(sh_name, shdr)| {
                if sh_name == ".stack" {
                    Some(shdr.sh_size as u32)
                } else {
                    None
                }
            })
        })
        // nothing in binary, use default
        .unwrap_or(2048);

    // Keep track of how much RAM this app will need.
    let mut minimum_ram_size: u32 = 0;

    // Find all segments destined for the RAM section that are stored in flash.
    // These are set in the linker file to consume memory, and we need to
    // account for them when we set the minimum amount of memory this app
    // requires.
    for segment in &elf_phdrs {
        // To filter, we need segments that are:
        // - Set to be LOADed.
        // - Have different virtual and physical addresses, meaning they are
        //   loaded into flash but actually reside in memory.
        // - Are not zero size in memory.
        // - Are writable (RAM should be writable).
        if segment.p_type == elf::abi::PT_LOAD
            && segment.p_vaddr != segment.p_paddr
            && segment.p_memsz > 0
            && ((segment.p_flags & elf::abi::PF_W) > 0)
        {
            minimum_ram_size += segment.p_memsz as u32;
        }
    }
    if verbose {
        println!(
            "Min RAM size from segments in ELF: {} bytes",
            minimum_ram_size
        );
    }

    // Add in room the app is asking us to reserve for the stack and heaps to
    // the minimum required RAM size.
    minimum_ram_size +=
        align_to(stack_len, 8) + align_to(app_heap_len, 4) + align_to(kernel_heap_len, 4);

    ////////////////////////////////////////////////////////////////////////////
    // Determine fixed addresses this app must be loaded at
    ////////////////////////////////////////////////////////////////////////////

    // Check for fixed addresses.
    //
    // For the most reliable results, we expect that the linker script for the
    // app created two symbols which we can use to determine where the app
    // expects to be placed in flash and ram.
    //
    // - `_flash_origin`: The address in flash the app was compiled for.
    // - `_sram_origin`: The address in ram the app was compiled for.
    //
    // For RAM, we use this method because there does not seem to be a reliable
    // method to extract the RAM start address from the elf. Since nothing
    // _actually_ has to be loaded into RAM, the ELF file does not have to keep
    // track of the first address in RAM. Further, Tock apps typically put a
    // .stack section at the beginning of RAM, and the stack is just a memory
    // holder and doesn't contain any actual data. The start of RAM address will
    // almost certainly exist somewhere in the ELF, but reliably extracting it
    // from different ELFs linked with different toolchains from different
    // linker scripts would I think require resorting to a bit of heuristics and
    // guessing. To avoid the potential issues there, we instead require that a
    // `_sram_origin` symbol be present to explicitly mark the start of RAM.
    //
    // For flash, we use the `_flash_origin` symbol if the linker script
    // includes it. In theory, we can deduce the start address of flash based on
    // the physaddr of segments. However, in some cases the linker appears to
    // place segments _before_ the start of flash. Note, it always seems to
    // place _sections_ within the specified flash region, but, at this point,
    // it is increasing untenable to reliably detect the start address of flash
    // based on segments and sections alone. To essentially sidestep this issue,
    // we default to passing the flash start address via the `_flash_origin`
    // symbol.
    //
    // If the elf doesn't include the `_flash_origin` symbol, we look at
    // loadable segments in the ELF, and find the segment with the lowest
    // address that is both executable and non-zero in file size. Since this is
    // a segment that must be loaded to execute the application, we assume this
    // is the start address of flash.
    //
    // In both case we check to see if the address matches our expected PIC
    // addresses:
    // - RAM: 0x00000000
    // - flash: 0x80000000
    //
    // These addresses are a Tock convention and enables PIC fixups to be done
    // by the app when it first starts. If for some reason an app is PIC and
    // wants to use different dummy PIC addresses, then this logic will have to
    // be updated.
    let mut fixed_address_flash: Option<u32> = None;
    let mut fixed_address_ram: Option<u32> = None;
    let mut fixed_address_flash_pic: bool = false;

    // Do flash address.

    // Try to get the flash address via the `_flash_origin` symbol.
    let flash_origin_address = if let Ok(Some((symtab, sym_strtab))) = elf_file.symbol_table() {
        // We are looking for the `_flash_origin` symbol and its value. If it
        // exists, this tells us the first address of flash when the app was
        // compiled.
        if let Some(flash_origin) = symtab.iter().find(|sym| {
            let name = sym_strtab
                .get(sym.st_name as usize)
                .expect("Failed to parse symbol name");
            name == "_flash_origin"
        }) {
            Some(flash_origin.st_value as u32)
        } else {
            None
        }
    } else {
        None
    };

    // Figure out if this is a PIC app or not, and if we couldn't find the
    // symbol then we estimate the address from segments.
    if let Some(flash_origin) = flash_origin_address {
        if flash_origin == 0x80000000 {
            // Matches the PIC address.
            fixed_address_flash_pic = true;
        } else {
            // We are a fixed address app, so we just use the given address.
            fixed_address_flash = Some(flash_origin)
        }
    } else {
        // We didn't find the symbol, so estimate from the segments.
        for segment in &elf_phdrs {
            // Only consider nonzero segments which are set to be loaded.
            if segment.p_type != elf::abi::PT_LOAD || segment.p_filesz == 0 {
                continue;
            }

            // Flash segments have to be marked executable, and we only care about
            // segments that actually contain data to be loaded into flash.
            if (segment.p_flags & elf::abi::PF_X) > 0
                && section_exists_in_segment(&elf_sections, segment)
            {
                // If this is standard Tock PIC, then this virtual address will be
                // at 0x80000000. Otherwise, we interpret this to mean that the
                // binary was compiled for a fixed address in flash. Once we confirm
                // this we do not need to keep checking.
                if segment.p_vaddr == 0x80000000 || fixed_address_flash_pic {
                    fixed_address_flash_pic = true;
                } else {
                    // We need to see if this segment represents the lowest
                    // address in flash that we are going to specify this app
                    // needs to be loaded at. To do this we compare this segment
                    // to any previous and keep track of the lowest address.
                    let segment_start = segment.p_paddr as u32;

                    fixed_address_flash = match fixed_address_flash {
                        Some(prev_addr) => Some(cmp::min(segment_start, prev_addr)),
                        None => {
                            // We found our first valid segment and haven't set
                            // our lowest address yet, so we do that now.
                            Some(segment_start)
                        }
                    };
                }
            }
        }
    }

    // Use the flags to see if we got PIC sections, and clear any other fixed
    // addresses we may have found.
    if fixed_address_flash_pic {
        fixed_address_flash = None;
    }

    // Do RAM address.
    // Get the symbol table section if it exists.
    if let Ok(Some((symtab, sym_strtab))) = elf_file.symbol_table() {
        // We are looking for the `_sram_origin` symbol and its value.
        // If it exists, we try to use it. Otherwise, we just do not try
        // to find a fixed RAM address.
        if let Some(sram_origin) = symtab.iter().find(|sym| {
            let name = sym_strtab
                .get(sym.st_name as usize)
                .expect("Failed to parse symbol name");
            name == "_sram_origin"
        }) {
            let sram_origin_address = sram_origin.st_value as u32;
            if sram_origin_address != 0x00000000 {
                fixed_address_ram = Some(sram_origin_address);
            }
        }
    }

    ////////////////////////////////////////////////////////////////////////////
    // Create the TBF header
    ////////////////////////////////////////////////////////////////////////////

    // We need to reserve space for the writeable flash region information in
    // the header, so we need to know how many writeable flash regions are in
    // this app. Iterate the segments of the ELF file and then iterate sections
    // within that segment to find sections with ".wfr" in the name.
    let mut writeable_flash_regions_count: usize = 0;
    for segment in &elf_phdrs {
        // Only consider segments which are set to be loaded.
        if segment.p_type != elf::abi::PT_LOAD || segment.p_filesz == 0 {
            continue;
        }

        // We only want nonzero sections within a segment.
        for (sh_name, shdr) in elf_sections.iter() {
            if shdr.sh_size > 0 && section_in_segment(shdr, segment) && sh_name.contains(".wfr") {
                writeable_flash_regions_count += 1;
            }
        }
    }
    if verbose {
        println!(
            "Number of writeable flash regions: {}",
            writeable_flash_regions_count
        );
    }

    // Additional debug information.
    if verbose {
        if let Some((major, minor)) = kernel_version {
            println!("Kernel version: {}.{}", major, minor);
        }
    }

    // Now we can create the first pass TBF header. This is mostly to get the
    // size of the header since we have to fill in some of the offsets later.
    let mut tbfheader = header::TbfHeader::new();

    // Set the binary end offset here because it will cause a program header to
    // be inserted. This ensures the length calculations for the binary will be
    // correct.
    tbfheader.set_binary_end_offset(0);
    tbfheader.set_app_version(app_version);

    let header_length = tbfheader.create(
        minimum_ram_size,
        writeable_flash_regions_count,
        package_name.clone(),
        fixed_address_ram,
        fixed_address_flash,
        permissions,
        storage_ids,
        kernel_version,
        short_id,
        Some(is_shared_library),
        shlib_dep_names,
        disabled,
    );

    ////////////////////////////////////////////////////////////////////////////
    // Adjust the protected region size to make fixed address work
    ////////////////////////////////////////////////////////////////////////////

    // Applications can hint a desired protected region size to elf2tab by
    // defining a special `tbf_protected_region_size` symbol:
    let protected_region_size_symbol =
        if let Ok(Some((symtab, sym_strtab))) = elf_file.symbol_table() {
            // We are looking for the `tbf_protected_region_size` symbol and its
            // value. If it exists, we can use it as a hint for the protected
            // region size.
            symtab
                .iter()
                .find(|sym| {
                    let name = sym_strtab
                        .get(sym.st_name as usize)
                        .expect("Failed to parse symbol name");
                    name == "tbf_protected_region_size"
                })
                .map(|tbf_header_sym| tbf_header_sym.st_value as u32)
        } else {
            None
        };

    // Determine the protected region size by checking the following sources in
    // this order:
    //
    // 1. Check for a `tbf_protected_region_size` symbol in the ELF file.
    //
    // 2. Use a fixed protected region size if one was passed through a command
    //    line argument.
    //
    // 3. Set the protected region size to fit the TBF headers. For non-PIC
    //    apps, align the start of the generated TBF file on a 256-byte
    //    boundary, based on the binary's fixed flash address.
    let protected_region_size =
        if let Some(fixed_protected_region_size) = protected_region_size_symbol {
            // The protected region size was specified in the ELF file through
            // the special `tbf_protected_region_size` symbol.
            //
            // If we have also been passed a fixed protected region size on the
            // command line, warn that the ELF symbol will take precedence!
            if protected_region_size_arg.is_some() {
                println!(
                    "Overriding command-line specified protected_region_size \
		 with tbf_protected_region_size symbol = {} bytes!",
                    fixed_protected_region_size
                );
            }

            fixed_protected_region_size
        } else if let Some(fixed_protected_region_size) = protected_region_size_arg {
            // A desired protected region size was specified on the command line:
            fixed_protected_region_size
        } else {
            // The protected region was neither specified on the command line,
            // nor as part of the ELF file. Normally, we default to an
            // additional size of 0 for the protected region beyond the
            // header. However, if we are _not_ doing PIC (as enforced in the
            // check above), we might want to choose a nonzero sized protected
            // region. Without PIC, the application binary must be at specific
            // address. In addition, boards have a fixed address where they
            // start looking for applications. To make both of those addresses
            // match, we can expand the protected region.
            //
            // /----- Protected Region ----------------\
            // |------------|------------------------- |---------------------
            // | TBF Header | Protected Region Trailer | Application Binary
            // |------------|--------------------------|---------------------
            // ^                           ^           ^
            // |                           |           |-- Fixed binary address
            // |-- Start of apps address   |-- Flexible size
            //
            //
            // An app may be positioned after another app in flash, and so the
            // start address is actually the start of apps address plus the size
            // of the first app. Tockloader can check for these addresses and
            // expand the protected region when it loads the app. But, in some
            // cases it is easier to just be able to flash the TBF directly onto
            // the board without needing Tockloader. So, we at least try to pick
            // a reasonable protected size in the non-PIC case to give the TBF a
            // chance of working as created.
            //
            // So, we put the start address of the TBF header at an alignment of
            // 256 if the application binary is at the expected address.
            if !fixed_address_flash_pic {
                // Non-PIC case. As a reasonable guess we try to get our TBF
                // start address to be at a 256 byte alignment.
                let app_binary_address = fixed_address_flash.unwrap_or(0); // Already checked for `None`.
                let tbf_start_address = util::align_down(app_binary_address, 256);
                app_binary_address - tbf_start_address
            } else {
                // Normal PIC case, no need to insert extra protected region.
                header_length as u32
            }
        };

    if verbose {
        println!("Protected region size: {} bytes", protected_region_size);
        println!("Header length: {} bytes", header_length);
    }

    // Validate that the protected region size at the very least fits our TBF
    // headers:
    if protected_region_size < header_length as u32 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "protected_region_size = {} is too small for the TBF headers. Header size: {}",
                protected_region_size, header_length
            ),
        ));
    }

    // Indicate an additional protected region size in the final TBF binary,
    // such that Tock can set its memory protection accordingly:
    if protected_region_size > header_length as u32 {
        if verbose {
            println!(
                "Inserting nonzero protected region trailer of length: {} \
		 bytes, protected region size: {} bytes.",
                protected_region_size - header_length as u32,
                protected_region_size,
            );
        }
        tbfheader.set_protected_size(protected_region_size - header_length as u32);
    }

    ////////////////////////////////////////////////////////////////////////////
    // Create the actual binary to include in the TBF
    ////////////////////////////////////////////////////////////////////////////

    // Need a place to put the app sections before we know the true TBF header.
    // This includes everything after the TBF header.
    let mut binary: Vec<u8> = Vec::new();

    // Keep track of an index from the beginning of the TBF binary of where we
    // are in creating the TBF binary.
    let mut binary_index = 0;

    // Add in padding for the protected region size beyond the actual TBF header
    // size and increment our index counter past the protected region.
    binary.extend(vec![0; protected_region_size as usize - header_length]);
    binary_index += protected_region_size as usize;

    // The init function is where the app will start executing, defined as an
    // offset from the end of protected region at the beginning of the app in
    // flash. Typically the protected region only includes the TBF header. To
    // calculate the offset we need to find which section includes the entry
    // function and then determine its offset relative to the end of the
    // protected region.
    let mut init_fn_offset: Option<u32> = None;

    // Need a place to put relocation data.
    let mut relocation_binary: Vec<u8> = Vec::new();

    // Keep track of the end address of the last segment (once we have a first
    // segment). This allows us to insert padding between segments as necessary.
    let mut last_segment_address_end: Option<usize> = None;

    // Address of the .got section in the output TBF file
    let mut got_address_in_tbf: Option<usize> = None;

    // Iterate over ELF's Program Headers to assemble the binary image as a
    // contiguous memory block. Only take into consideration segments where
    // filesz is greater than 0.
    for segment in &mut elf_phdrs {
        // Only consider segments which are set to be loaded.
        if segment.p_type != elf::abi::PT_LOAD {
            continue;
        }

        // Do not include segments with zero size, as these likely go in memory,
        // not flash.
        if segment.p_filesz == 0 {
            continue;
        }

        // Check if the segment starts entirely before the start of flash. If
        // so, skip this segment.
        if let Some(flash_address) = fixed_address_flash {
            let flash_address: u64 = flash_address as u64;
            if segment.p_paddr + segment.p_filesz < flash_address {
                continue;
            }
        }

        // It's possible the linker started this segment _before_ the start of
        // the flash region. We edit the segment to remove the portion that
        // starts before the start of flash.
        if let Some(flash_address) = fixed_address_flash {
            let flash_address: u64 = flash_address as u64;
            if segment.p_paddr < flash_address {
                // We need to truncate the start of the segment.
                let truncate_length = flash_address - segment.p_paddr;

                segment.p_offset += truncate_length;
                segment.p_paddr += truncate_length;
                segment.p_vaddr += truncate_length;
                segment.p_filesz -= truncate_length;
                segment.p_memsz -= truncate_length;
            }
        }

        // Insert padding between segments if needed.
        if let Some(last_segment_address_end) = last_segment_address_end {
            // We have a previous segment. Now, check if there is any padding
            // between the segments in the .elf.
            let chk_padding = (segment.p_paddr as usize).checked_sub(last_segment_address_end);

            if let Some(padding) = chk_padding {
                if padding > 0 {
                    if verbose {
                        println!("  Including padding between segments size={}", padding);
                    }

                    if padding >= 4096 {
                        // Warn the user that we're inserting a large amount of
                        // padding (>= 4096, which is the ELF file segment padding)
                        // into the binary. This can be a sign of an incorrect /
                        // broken ELF file (where not all LOADed non-zero sized
                        // sections are marked to be loaded from flash).
                        println!("  Warning! Inserting a large amount of padding.");
                    }

                    // Insert the padding into the generated binary.
                    binary.extend(vec![0; padding]);
                    binary_index += padding;
                }
            } else {
                println!(
                    "  Warning! Expecting ELF sections to be in physical (load) address order."
                );
                println!("           Not inserting padding, the resulting TBF may be broken.");
            }
        }

        if verbose {
            println!(
                "  Adding segment. Offset: {0} ({0:#x}). Length: {1} ({1:#x}) bytes.",
                binary_index, segment.p_filesz
            );
        }

        // Read the segment from the ELF and append to the output binary.
        let mut content: Vec<u8> = vec![0; (segment.p_filesz) as usize];
        input_file
            .seek(SeekFrom::Start(segment.p_offset))
            .expect("unable to seek input ELF file");
        input_file
            .read_exact(&mut content)
            .expect("failed to read segment data");

        let start_segment = segment.p_paddr;
        let end_segment = segment.p_paddr + segment.p_filesz;

        // Check if this segment contains the entry point, and calculate the
        // offset we need to store in the TBF header if so.
        if elf_file.ehdr.e_entry >= start_segment && elf_file.ehdr.e_entry < end_segment {
            if init_fn_offset.is_some() {
                // If the app is disabled just report a warning if we find two
                // entry points. OTBN apps will contain two entry points, so
                // this allows us to load them.
                if disabled {
                    if verbose {
                        println!("Duplicate entry point in Program Segments");
                    }
                } else {
                    panic!("Duplicate entry point in Program Segments");
                }
            } else {
                // Get the position of the entry point in the segment.
                let entry_offset = (elf_file.ehdr.e_entry - start_segment) as usize;
                // `init_fn_offset` is the offset from the end of the TBF header
                // to the entry point within the application binary.
                let tbf_entry_offset = (binary_index + entry_offset - header_length) as u32;
                // Set the init_fn in the header.
                tbfheader.set_init_fn_offset(tbf_entry_offset);
                // Save it in case we find multiple entry points.
                init_fn_offset = Some(tbf_entry_offset);
            }
        }

        // Iterate all sections that are in the segment we just loaded.
        //
        // We need two things:
        // 1. To find all relevant relocation data we need to add.
        // 2. To find if there are any writeable flash regions we need to set in
        //    the TBF header.
        for (sh_name, shdr) in elf_sections.iter() {
            // Skip zero size sections.
            if shdr.sh_size == 0 {
                continue;
            }

            // Check if this section is within the segment.
            if section_in_segment(shdr, segment) {
                if sh_name == ".got" {
                    got_address_in_tbf = Some(binary_index + (shdr.sh_offset - segment.p_offset) as usize);
                    if verbose {
                        println!("GOT located at 0x{:x} in original ELF file", shdr.sh_addr);
                        println!("\t Located at 0x{:x} in TBF file", got_address_in_tbf.unwrap());
                        println!("\t binary_index = 0x{:x}; shdr.sh_offset = 0x{:x}; segment.p_offset = 0x{:x};", binary_index, shdr.sh_offset, segment.p_offset);
                    }
                }
                // This section is in this segment.
                if verbose {
                    println!(
                        "    Contains section {0}. Offset: {1} ({1:#x}). Length: {2} ({2:#x}) bytes.",
                        sh_name,
                        binary_index + (shdr.sh_offset - segment.p_offset) as usize,
                        shdr.sh_size
                    );
                }

                // First, determine if we need to check for relocation data for
                // this section. The section must be marked `SHF_WRITE`, as to
                // use the relocations at runtime requires being able to update
                // the contents of the section.
                if shdr.sh_flags as u32 & elf::abi::SHF_WRITE > 0 {
                    // Then check if there is a ".rel.<section name>" section
                    // that we need to include in the relocation data.

                    // relocation_section_name = ".rel" + section_name
                    let mut relocation_section_name: String = ".rel".to_owned();
                    relocation_section_name.push_str(sh_name);

                    // Get the contents of the relocation data if it exists and
                    // add that data to a buffer of relocation data.
                    let rel_data = elf_sections
                        .iter()
                        .find(|(sh_name, _)| *sh_name == relocation_section_name)
                        .map_or(&[] as &[u8], |(_, shdr)| {
                            elf_file.section_data(shdr).map_or(&[], |(data, _)| data)
                        });
                    relocation_binary.extend(rel_data);

                    if verbose && !rel_data.is_empty() {
                        println!(
                            "      Including relocation data ({0}). Length: {1} ({1:#x}) bytes.",
                            relocation_section_name,
                            rel_data.len(),
                        );
                    }
                }

                if is_shared_library == 1 {
                    let rel_data = elf_sections
                        .iter()
                        .find(|(sh_name, _)| *sh_name == ".rel.text")
                        .map(|(_, shdr)| {
                            elf_file.section_data_as_rels(shdr)
                            // elf_file.section_data(shdr).map_or(&[], |(data, _)| data)
                        });

                    if let Some(Ok(rels)) = rel_data {
                        for rel in rels.into_iter() {
                            println!("r_type is {}", rel.r_type);
                        };
                    };
                }


                // Second, check if this is a writeable flash region and if so,
                // include its details in the TBF header.
                if sh_name.contains(".wfr") {
                    // Calculate where this .wfr section is in the segment.
                    let wfr_offset = (shdr.sh_addr - segment.p_vaddr) as usize;
                    // Calculate the position of the writeable flash region in
                    // the TBF binary.
                    let wfr_position = binary_index + wfr_offset;

                    // Use these values to update the TBF header.
                    tbfheader.set_writeable_flash_region_values(
                        wfr_position as u32,
                        shdr.sh_size as u32,
                    );
                }
            }
        }

        // Save the end of this segment so we can check if padding is required
        // between segments.
        last_segment_address_end = Some(end_segment as usize);

        binary.extend(content);
        binary_index += segment.p_filesz as usize;
    }

    // Now that we know where the end of the section data is, we can check for
    // alignment.
    if !relocation_binary.is_empty() && amount_alignment_needed(binary_index as u32, 4) != 0 {
        println!(
            "Warning! Placing relocation data at {:#x}, which is not 4-byte aligned.",
            binary_index
        );
    }

    // Add 4 bytes for the relocation data length and the size of the relocation
    // data to our total length.
    binary_index += mem::size_of::<u32>() + relocation_binary.len();

    ////////////////////////////////////////////////////////////////////////////
    // Create the TBF footer
    ////////////////////////////////////////////////////////////////////////////

    // Next up is the footer. Since we know where the footer starts, we can
    // record that now. Also insert app version number.
    tbfheader.set_binary_end_offset(binary_index as u32);
    tbfheader.set_app_version(app_version);

    // Process optional footers
    if sha256 {
        binary_index += mem::size_of::<header::TbfHeaderTlv>();
        binary_index += mem::size_of::<header::TbfFooterCredentialsType>();
        binary_index += 32; // SHA256 is 32 bytes long
    }

    if sha384 {
        binary_index += mem::size_of::<header::TbfHeaderTlv>();
        binary_index += mem::size_of::<header::TbfFooterCredentialsType>();
        binary_index += 48; // SHA384 is 48 bytes long
    }

    if sha512 {
        binary_index += mem::size_of::<header::TbfHeaderTlv>();
        binary_index += mem::size_of::<header::TbfFooterCredentialsType>();
        binary_index += 64; // SHA512 is 64 bytes long
    }

    if rsa4096_private_key.is_some() {
        binary_index += mem::size_of::<header::TbfHeaderTlv>();
        binary_index += mem::size_of::<header::TbfFooterCredentialsType>();
        binary_index += 1024;
    }

    let footers_initial_len = binary_index - tbfheader.binary_end_offset() as usize;

    // Flag to track if we are guaranteed to have a reserved space footer.
    let mut ensured_footer_reserved_space: bool = false;

    // Make sure the footer is at least the minimum requested size.
    if (minimum_footer_size as usize) > footers_initial_len {
        let mut needed_footer_reserved_space = (minimum_footer_size as usize) - footers_initial_len;

        // We can only add reserved space to the footer with a minimum of 8
        // bytes.
        needed_footer_reserved_space = cmp::max(
            needed_footer_reserved_space,
            mem::size_of::<header::TbfHeaderTlv>()
                + mem::size_of::<header::TbfFooterCredentialsType>(),
        );
        // We also must ensure that if there were to be a TLV after the
        // reserved TLV that it would start at a 4 byte alignment.
        needed_footer_reserved_space = align_to(needed_footer_reserved_space as u32, 4) as usize;

        // Add reserved space to the footer.
        binary_index += needed_footer_reserved_space;

        // Since we ensured there is room for the reserved space footer, we mark
        // that that footer will be created.
        ensured_footer_reserved_space = true;
    }

    // Optionally calculate the additional padding needed to ensure the app size
    // meets the padding requirements.
    //
    // This will be largely covered with a footer reservation. The
    // `post_content_pad` is any additional space that cannot be handled by
    // reserved space in the footer.
    let post_content_pad = trailing_padding.map_or(0, |padding_type| {
        // Calculate how many additional bytes we need to add to meet length
        // requirement.
        let pad = match padding_type {
            TrailingPadding::TotalSizePowerOfTwo => {
                // Pad binary to the next power of two, but not less than 512
                // bytes.
                if binary_index.count_ones() > 1 {
                    let power2len =
                        cmp::max(1 << (32 - (binary_index as u32).leading_zeros()), 512);
                    power2len - binary_index
                } else {
                    0
                }
            }
            TrailingPadding::TotalSizeMultiple(multiple) => {
                (multiple - (binary_index % multiple)) % multiple
            }
        };

        // Increment to include the padding.
        binary_index += pad;

        // If there is room for a TbfFooterCredentials we will use that.
        if ensured_footer_reserved_space
            || pad
                >= (mem::size_of::<header::TbfHeaderTlv>()
                    + mem::size_of::<header::TbfFooterCredentialsType>())
        {
            0
        } else {
            // Otherwise need to include the padding.
            pad
        }
    });

    let total_size = binary_index;

    // Now set the total size of the app in the header.
    tbfheader.set_total_size(total_size as u32);

    if verbose {
        print!("{}", tbfheader);
    }

    // Write the header and actual app to a binary file.
    output.write_all(tbfheader.generate().unwrap().get_ref())?;
    output.write_all(binary.as_ref())?;

    let rel_data_len: [u8; 4] = (relocation_binary.len() as u32).to_le_bytes();
    if verbose {
        println!("Relocation data length: {}", relocation_binary.len());
    }
    output.write_all(&rel_data_len)?;
    output.write_all(relocation_binary.as_ref())?;

    // That is everything that we are going to include in the app binary
    // that is covered by integrity. Now add footers.

    let footers_len = total_size - tbfheader.binary_end_offset() as usize;
    let mut footer_space_remaining = footers_len;
    if sha256 {
        // Total length
        let sha256_len = mem::size_of::<header::TbfHeaderTlv>()
            + mem::size_of::<header::TbfFooterCredentialsType>()
            + 32; // SHA256 is 32 bytes long
                  // Length in the TLV field
        let sha256_tlv_len = sha256_len - mem::size_of::<header::TbfHeaderTlv>();

        let mut hasher = Sha256::new();
        hasher.update(&output[0..tbfheader.binary_end_offset() as usize]);
        let result = hasher.finalize();
        let sha_credentials = header::TbfFooterCredentials {
            base: header::TbfHeaderTlv {
                tipe: header::TbfHeaderTypes::Credentials,
                length: sha256_tlv_len as u16,
            },
            format: header::TbfFooterCredentialsType::SHA256,
            data: result.to_vec(),
        };
        output.write_all(sha_credentials.generate().unwrap().get_ref())?;
        footer_space_remaining -= sha256_len;
        if verbose {
            println!("Added SHA256 credential.");
        }
    }

    if sha384 {
        // Total length
        let sha384_len = mem::size_of::<header::TbfHeaderTlv>()
            + mem::size_of::<header::TbfFooterCredentialsType>()
            + 48; // SHA384 is 48 bytes long
                  // Length in the TLV field
        let sha384_tlv_len = sha384_len - mem::size_of::<header::TbfHeaderTlv>();

        let mut hasher = Sha384::new();
        hasher.update(&output[0..tbfheader.binary_end_offset() as usize]);
        let result = hasher.finalize();
        let sha_credentials = header::TbfFooterCredentials {
            base: header::TbfHeaderTlv {
                tipe: header::TbfHeaderTypes::Credentials,
                length: sha384_tlv_len as u16,
            },
            format: header::TbfFooterCredentialsType::SHA384,
            data: result.to_vec(),
        };
        output.write_all(sha_credentials.generate().unwrap().get_ref())?;
        footer_space_remaining -= sha384_len;
        if verbose {
            println!("Added SHA384 credential.");
        }
    }

    if sha512 {
        // Total length
        let sha512_len = mem::size_of::<header::TbfHeaderTlv>()
            + mem::size_of::<header::TbfFooterCredentialsType>()
            + 64; // SHA512 is 64 bytes long
                  // Length in the TLV field
        let sha512_tlv_len = sha512_len - mem::size_of::<header::TbfHeaderTlv>();

        let mut hasher = Sha512::new();
        hasher.update(&output[0..tbfheader.binary_end_offset() as usize]);
        let result = hasher.finalize();
        let sha_credentials = header::TbfFooterCredentials {
            base: header::TbfHeaderTlv {
                tipe: header::TbfHeaderTypes::Credentials,
                length: sha512_tlv_len as u16,
            },
            format: header::TbfFooterCredentialsType::SHA512,
            data: result.to_vec(),
        };
        output.write_all(sha_credentials.generate().unwrap().get_ref())?;
        footer_space_remaining -= sha512_len;
        if verbose {
            println!("Added SHA512 credential.");
        }
    }

    if rsa4096_private_key.is_some() {
        let rsa4096_len = mem::size_of::<header::TbfHeaderTlv>()
            + mem::size_of::<header::TbfFooterCredentialsType>()
            + 1024; // Signature + key is 1024 bytes long
                    // Length in the TLV field
        let rsa4096_tlv_len = rsa4096_len - mem::size_of::<header::TbfHeaderTlv>();

        let private_key_path_str = rsa4096_private_key.unwrap();
        let private_key_path = Path::new(&private_key_path_str);
        let private_key_contents = read_rsa_file(private_key_path).unwrap_or_else(|e| {
            panic!(
                "Failed to read private key from {:?}: {:?}",
                private_key_path, e
            );
        });

        let key_pair = ring::signature::RsaKeyPair::from_pkcs8(&private_key_contents)
            .unwrap_or_else(|e| {
                panic!("RSA4096 could not be parsed: {:?}", e);
            });

        let public_key: ring::signature::RsaPublicKeyComponents<Vec<u8>> =
            ring::signature::RsaPublicKeyComponents {
                n: key_pair
                    .public_key()
                    .modulus()
                    .big_endian_without_leading_zero()
                    .to_vec(),
                e: key_pair
                    .public_key()
                    .exponent()
                    .big_endian_without_leading_zero()
                    .to_vec(),
            };

        if key_pair.public_modulus_len() != 512 {
            // A 4096-bit key should have a 512-byte modulus
            panic!(
                "RSA4096 signature requested but key {:?} is not 4096 bits, it is {} bits",
                private_key_path,
                key_pair.public_modulus_len() * 8
            );
        }
        let rng = rand::SystemRandom::new();
        let mut signature = vec![0; key_pair.public_modulus_len()];
        let _res = key_pair
            .sign(
                &signature::RSA_PKCS1_SHA512,
                &rng,
                &output[0..tbfheader.binary_end_offset() as usize],
                &mut signature,
            )
            .map_err(|e| {
                panic!("Could not generate RSA4096 signature: {:?}", e);
            });
        let mut credentials = vec![0; 1024];
        credentials[..key_pair.public_modulus_len()]
            .copy_from_slice(&public_key.n[..key_pair.public_modulus_len()]);
        for (i, sig) in signature.iter().enumerate() {
            let index = i + key_pair.public_modulus_len();
            credentials[index] = *sig;
        }

        let rsa4096_credentials = header::TbfFooterCredentials {
            base: header::TbfHeaderTlv {
                tipe: header::TbfHeaderTypes::Credentials,
                length: rsa4096_tlv_len as u16,
            },
            format: header::TbfFooterCredentialsType::Rsa4096Key,
            data: credentials,
        };
        output.write_all(rsa4096_credentials.generate().unwrap().get_ref())?;
        footer_space_remaining -= rsa4096_len;
        if verbose {
            println!("Added PKCS#1v1.5 RSA4096 signature credential.");
        }
    }

    let padding_len = footer_space_remaining;

    // Need at least space for the base Credentials TLV.
    if padding_len
        >= (mem::size_of::<header::TbfHeaderTlv>()
            + mem::size_of::<header::TbfFooterCredentialsType>())
    {
        let padding_tlv_len = padding_len - mem::size_of::<header::TbfHeaderTlv>();
        let reserved_len = padding_tlv_len - mem::size_of::<header::TbfFooterCredentialsType>();
        let reserved_vec = vec![0u8; reserved_len];
        let padding_credentials = header::TbfFooterCredentials {
            base: header::TbfHeaderTlv {
                tipe: header::TbfHeaderTypes::Credentials,
                length: padding_tlv_len as u16,
            },
            format: header::TbfFooterCredentialsType::Reserved,
            data: reserved_vec,
        };
        let creds = padding_credentials.generate().unwrap();
        output.write_all(creds.get_ref())?;
    }

    // Pad to get a power of 2 sized flash app, if requested.
    util::do_pad(output, post_content_pad)?;

    let app_relocs = get_fn_relocs(verbose, &elf_sections, &elf_file, &elf_file_buf, got_address_in_tbf.unwrap()).unwrap_or_default();
    output_relocation_file(verbose, shlib_deps, app_relocs, &package_name, output_relocation)?;

    Ok(())
}
