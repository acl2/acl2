        ;; 32-bit XOR instruction: XOR EAX, imm32
        ;; Encoding: 35 id (35 E8 03 00 00)  [5 bytes]

        global _start

        section .text
_start:
        xor     eax, 1000
        ret
