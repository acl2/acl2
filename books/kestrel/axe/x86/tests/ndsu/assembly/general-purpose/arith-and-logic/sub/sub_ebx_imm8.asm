        ;; 32-bit SUB general register sign-extended imm8: SUB EBX, imm8
        ;; Encoding: 83 /5 ib = 83 EB 05  [3 bytes]

        global _start

        section .text
_start:
        sub     ebx, 5
        ret
