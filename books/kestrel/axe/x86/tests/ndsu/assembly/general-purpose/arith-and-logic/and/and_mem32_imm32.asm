        ;; 32-bit AND immediate to memory: AND [RBX], imm32
        ;; Encoding: 81 /4 id = 81 23 E8 03 00 00  [6 bytes]

        global _start

        section .text
_start:
        and     dword [rbx], 1000
