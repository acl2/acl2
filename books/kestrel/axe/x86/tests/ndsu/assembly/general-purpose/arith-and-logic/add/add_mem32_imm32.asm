        ;; 32-bit ADD immediate to memory: ADD [RBX], imm32
        ;; Encoding: 81 /0 id = 81 03 E8 03 00 00  [6 bytes]

        global _start

        section .text
_start:
        add     dword [rbx], 1000
