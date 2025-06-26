#!/usr/bin/env bash
./target/release/elf2tab -n libtest --stack 2048 --app-heap 1024 --kernel-heap 1024 --kernel-major 2 --kernel-minor 0 --minimum-footer-size 3000 -v -o libtest.tab ../libtock-c/libtest/build/cortex-m4/cortex-m4.so
