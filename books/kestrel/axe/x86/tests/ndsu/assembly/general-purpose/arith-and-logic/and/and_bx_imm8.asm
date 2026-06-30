        ;; 16-bit AND instruction: AND BX, imm8 (sign-extended)
        ;; Encoding: 66 83 /4 ib (66 83 E3 05)  [4 bytes]
        ;; The immediate 5 is sign-extended from 8 to 16 bits; since 5 > 0 and 5 < 128, value is 5.

        global _start

        section .text
_start:
        and     bx, 5
        ret
