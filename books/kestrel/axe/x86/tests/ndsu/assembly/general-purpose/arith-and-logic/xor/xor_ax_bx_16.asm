        ;; 16-bit XOR instruction: XOR AX, BX
        ;; Encoding: 66 31 /r (66 31 D8)  [3 bytes]

        global _start

        section .text
_start:
        xor     ax, bx
        ret
