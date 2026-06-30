        ;; 32-bit OR immediate to memory: OR [RBX], imm32
        ;; Encoding: 81 /1 id = 81 0B E8 03 00 00  [6 bytes]

        global _start

        section .text
_start:
        or      dword [rbx], 1000
