        ;; 64-bit SUB general register sign-extended imm8: SUB RBX, imm8
        ;; Encoding: REX.W 83 /5 ib = 48 83 EB 05  [4 bytes]

        global _start

        section .text
_start:
        sub     rbx, 5
        ret
