Axe tests created by NDSU.

================================================================================

Information on how these files were built:

;; Done on Kestrel machine peregrine:

gcc adc-CF.c -o adc-CF.elf64

gcc add-commutative.c -o add-commutative.elf64

gcc and-CF.c -o and-CF.elf64
gcc and-OF.c -o and-OF.elf64
gcc and-PF.c -o and-PF.elf64
gcc and-SF.c -o and-SF.elf64
gcc and-ZF.c -o and-ZF.elf64

gcc cmp-CF.c -o cmp-CF.elf64
gcc cmp-PF0.c -o cmp-PF0.elf64
gcc cmp-PF1.c -o cmp-PF1.elf64
gcc cmp-SF.c -o cmp-SF.elf64
gcc cmp-ZF.c -o cmp-ZF.elf64

gcc inc_dec.c -o inc_dec.elf64

gcc or-CF.c -o or-CF.elf64
gcc or-OF.c -o or-OF.elf64
gcc or-SF.c -o or-SF.elf64
gcc or-ZF.c -o or-ZF.elf64

gcc sub-CF.c -o sub-CF.elf64
gcc sub-OF.c -o sub-OF.elf64
gcc sub-PF0.c -o sub-PF0.elf64
gcc sub-PF1.c -o sub-PF1.elf64
gcc sub-SF.c -o sub-SF.elf64
gcc sub-ZF.c -o sub-ZF.elf64

gcc test-CF.c -o test-CF.elf64
gcc test-OF.c -o test-OF.elf64
gcc test-SF.c -o test-SF.elf64
gcc test-ZF.c -o test-ZF.elf64

gcc xor-CF.c -o xor-CF.elf64
gcc xor-OF.c -o xor-OF.elf64
gcc xor-SF.c -o xor-SF.elf64
gcc xor-ZF.c -o xor-ZF.elf64

===

gcc add.c -o add.elf64
gcc add-r-imm.c -o add-r-imm.elf64

gcc add-r32-m32.c -o add-r32-m32.elf64

;; Done on MacBook Pro Intel Quad-Core Intel Core i5

gcc -o add-imm.macho64 add-imm.c
gcc -o sub-imm.macho64 sub-imm.c

gcc -o add-all-configurations.macho64 add-all-configurations.c
gcc -o and.macho64 and.c
gcc -o or.macho64 or.c

;; Done on Dell Latitude 5480, Intel Core i5 64-bit Windows

gcc -o add-all-configurations.pe64 add-all-configurations.c
gcc -o and.pe64 and.c
gcc -o or.pe64 or.c