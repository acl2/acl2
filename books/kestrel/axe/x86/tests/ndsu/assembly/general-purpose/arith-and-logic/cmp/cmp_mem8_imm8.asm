        ;; 8-bit CMP immediate to memory: CMP [RBX], imm8
        ;; Encoding: 80 /7 ib = 80 3B 05  [3 bytes]

        global _start

        section .text
_start:
        cmp     byte [rbx], 5
