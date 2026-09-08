        ;; 8-bit XOR instruction: XOR AL, imm8
        ;; Encoding: 34 ib (34 05)  [2 bytes]

        global _start

        section .text
_start:
        xor     al, 5
        ret
