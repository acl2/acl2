Axe tests created by NDSU.

================================================================================

Information on how these files were built:

;; Done on Kestrel machine peregrine:

gcc adc-CF.c -o adc-CF.elf64

gcc add-commutative.c -o add-commutative.elf64

gcc add-AF.c -o add-AF.elf64
gcc add-CF.c -o add-CF.elf64
gcc add-OF.c -o add-OF.elf64
gcc 'add-PF=1.c' -o 'add-PF=1.elf64'
gcc 'add-PF=0.c' -o 'add-PF=0.elf64'
gcc add-SF.c -o add-SF.elf64
gcc add-ZF.c -o add-ZF.elf64

gcc and-CF.c -o and-CF.elf64
gcc and-SF.c -o and-SF.elf64
gcc and-ZF.c -o and-ZF.elf64

gcc inc_dec.c -o inc_dec.elf64

gcc or-CF.c -o or-CF.elf64
gcc or-SF.c -o or-SF.elf64
gcc or-ZF.c -o or-ZF.elf64

gcc sub-CF.c -o sub-CF.elf64
gcc sub-SF.c -o sub-SF.elf64
gcc sub-ZF.c -o sub-ZF.elf64

gcc test-CF.c -o test-CF.elf64
gcc test-SF.c -o test-SF.elf64
gcc test-ZF.c -o test-ZF.elf64

gcc xor-CF.c -o xor-CF.elf64
gcc xor-SF.c -o xor-SF.elf64
gcc xor-ZF.c -o xor-ZF.elf64
