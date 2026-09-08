        ;; 16-bit XOR instruction: XOR BX, imm8 (sign-extended)
        ;; Encoding: 66 83 /6 ib (66 83 F3 05)  [4 bytes]
        ;; The immediate 5 is sign-extended from 8 to 16 bits; since 5 > 0 and 5 < 128, value is 5.

        global _start

        section .text
_start:
        xor     bx, 5
        ret
