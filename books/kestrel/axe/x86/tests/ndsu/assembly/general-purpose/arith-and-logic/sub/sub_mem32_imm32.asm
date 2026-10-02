        ;; 32-bit SUB immediate to memory: SUB [RBX], imm32
        ;; Encoding: 81 /5 id = 81 2B E8 03 00 00  [6 bytes]

        global _start

        section .text
_start:
        sub     dword [rbx], 1000
