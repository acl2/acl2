        ;; 32-bit XOR instruction: XOR EBX, imm8 (sign-extended)
        ;; Encoding: 83 /6 ib (83 F3 05)  [3 bytes]
        ;; The immediate 5 is sign-extended from 8 to 32 bits; since 5 > 0 and 5 < 128, value is 5.

        global _start

        section .text
_start:
        xor     ebx, 5
        ret
