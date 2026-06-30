        ;; 16-bit AND instruction: AND BX, imm16
        ;; Encoding: 66 81 /4 iw (66 81 E3 2C 01)  [5 bytes]
        ;; Immediate 300 requires the full 16-bit form (81 /4 iw).

        global _start

        section .text
_start:
        and     bx, 300
        ret
