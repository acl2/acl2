        ;; 32-bit OR instruction: OR EBX, imm8 (sign-extended)
        ;; Encoding: 83 /1 ib (83 CB 05)  [3 bytes]
        ;; The immediate 5 is sign-extended from 8 to 32 bits; since 5 > 0 and 5 < 128, value is 5.

        global _start

        section .text
_start:
        or      ebx, 5
        ret
