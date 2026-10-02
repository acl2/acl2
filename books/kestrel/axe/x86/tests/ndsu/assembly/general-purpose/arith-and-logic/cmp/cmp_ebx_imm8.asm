        ;; 32-bit CMP general register sign-extended imm8: CMP EBX, imm8
        ;; Encoding: 83 /7 ib = 83 FB 05  [3 bytes]

        global _start

        section .text
_start:
        cmp     ebx, 5
        ret
