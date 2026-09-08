        ;; 16-bit SUB with sign-extended imm8: SUB [RBX], imm8 (sign-extended to 16 bits)
        ;; Encoding: 66 83 /5 ib = 66 83 2B 05  [4 bytes]

        global _start

        section .text
_start:
        sub     word [rbx], 5
