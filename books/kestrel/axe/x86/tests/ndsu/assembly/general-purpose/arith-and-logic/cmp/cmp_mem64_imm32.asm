        ;; 64-bit CMP immediate to memory: CMP [RBX], imm32 (sign-extended)
        ;; Encoding: REX.W 81 /7 id = 48 81 3B E8 03 00 00  [7 bytes]

        global _start

        section .text
_start:
        cmp     qword [rbx], 1000
