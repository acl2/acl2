        ;; 16-bit SUB general register sign-extended imm8: SUB BX, imm8
        ;; Encoding: 66 83 /5 ib = 66 83 EB 05  [4 bytes]

        global _start

        section .text
_start:
        sub     bx, 5
        ret
