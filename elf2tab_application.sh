#!/usr/bin/env bash
./target/release/elf2tab -n shlib_app --stack 2048 --app-heap 1024 --kernel-heap 1024 --kernel-major 2 --kernel-minor 0 --minimum-footer-size 3000 --shared_library_deps ../libtock-c/libtest/build/cortex-m4/libtest.so -v -o shlib_app.tab ../libtock-c/examples/shlib_app/build/cortex-m4/cortex-m4.elf
