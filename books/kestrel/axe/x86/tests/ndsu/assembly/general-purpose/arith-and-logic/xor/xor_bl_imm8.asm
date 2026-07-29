        ;; 8-bit XOR instruction: XOR BL, imm8
        ;; Encoding: 80 /6 ib (80 F3 05)  [3 bytes]

        global _start

        section .text
_start:
        xor     bl, 5
        ret
