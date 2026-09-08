        ;; 8-bit SUB immediate to memory: SUB [RBX], imm8
        ;; Encoding: 80 /5 ib = 80 2B 05  [3 bytes]

        global _start

        section .text
_start:
        sub     byte [rbx], 5
