        ;; 16-bit CMP immediate to memory: CMP [RBX], imm16
        ;; Encoding: 66 81 /7 iw = 66 81 3B 2C 01  [5 bytes]

        global _start

        section .text
_start:
        cmp     word [rbx], 300
