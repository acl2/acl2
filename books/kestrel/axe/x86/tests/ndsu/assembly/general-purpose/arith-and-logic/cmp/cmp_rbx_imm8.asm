        ;; 64-bit CMP general register sign-extended imm8: CMP RBX, imm8
        ;; Encoding: REX.W 83 /7 ib = 48 83 FB 05  [4 bytes]

        global _start

        section .text
_start:
        cmp     rbx, 5
        ret
