        ;; 32-bit XOR immediate to memory: XOR [RBX], imm32
        ;; Encoding: 81 /6 id = 81 33 E8 03 00 00  [6 bytes]

        global _start

        section .text
_start:
        xor     dword [rbx], 1000
