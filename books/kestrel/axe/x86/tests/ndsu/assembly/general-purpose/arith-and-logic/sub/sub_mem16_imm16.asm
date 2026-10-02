        ;; 16-bit SUB immediate to memory: SUB [RBX], imm16
        ;; Encoding: 66 81 /5 iw = 66 81 2B 2C 01  [5 bytes]

        global _start

        section .text
_start:
        sub     word [rbx], 300
