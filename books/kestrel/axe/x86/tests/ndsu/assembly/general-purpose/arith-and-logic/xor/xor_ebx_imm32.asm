        ;; 32-bit XOR instruction: XOR EBX, imm32
        ;; Encoding: 81 /6 id (81 F3 E8 03 00 00)  [6 bytes]

        global _start

        section .text
_start:
        xor     ebx, 1000
        ret
