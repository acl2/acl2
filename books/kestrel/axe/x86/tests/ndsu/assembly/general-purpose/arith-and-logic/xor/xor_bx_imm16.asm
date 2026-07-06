        ;; 16-bit XOR instruction: XOR BX, imm16
        ;; Encoding: 66 81 /6 iw (66 81 F3 2C 01)  [5 bytes]
        ;; Immediate 300 requires the full 16-bit form (81 /6 iw).

        global _start

        section .text
_start:
        xor     bx, 300
        ret
