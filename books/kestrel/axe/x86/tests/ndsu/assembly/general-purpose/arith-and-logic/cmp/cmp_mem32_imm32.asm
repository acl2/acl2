        ;; 32-bit CMP immediate to memory: CMP [RBX], imm32
        ;; Encoding: 81 /7 id = 81 3B E8 03 00 00  [6 bytes]

        global _start

        section .text
_start:
        cmp     dword [rbx], 1000
