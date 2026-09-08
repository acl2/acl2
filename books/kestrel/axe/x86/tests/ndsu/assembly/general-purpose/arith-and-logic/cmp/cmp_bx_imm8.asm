        ;; 16-bit CMP general register sign-extended imm8: CMP BX, imm8
        ;; Encoding: 66 83 /7 ib = 66 83 FB 05  [4 bytes]

        global _start

        section .text
_start:
        cmp     bx, 5
        ret
