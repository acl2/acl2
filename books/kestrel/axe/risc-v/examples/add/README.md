How the executable was created (on a Macbook Pro M2 Max):

/opt/homebrew/Cellar/riscv-gnu-toolchain/main/bin/riscv64-unknown-elf-gcc -march=rv32im -mabi=ilp32 add.c -o add.elf32