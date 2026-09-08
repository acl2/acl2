Done on Kestrel machine 'osprey':

nasm -f elf64 add.asm -o add.o
ld -o add.elf64 add.o

nasm -f elf32 add.asm -o add.o32
ld -m elf_i386 -o add.elf32 add.o32
