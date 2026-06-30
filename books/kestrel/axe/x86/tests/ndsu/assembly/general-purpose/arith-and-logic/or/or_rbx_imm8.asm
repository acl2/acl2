        ;; 64-bit OR instruction: OR RBX, imm8 (sign-extended)
        ;; Encoding: REX.W + 83 /1 ib (48 83 CB 05)  [4 bytes]
        ;; The immediate 5 is sign-extended from 8 to 64 bits; since 5 > 0 and 5 < 128, value is 5.

        global _start

        section .text
_start:
        or      rbx, 5
        ret
