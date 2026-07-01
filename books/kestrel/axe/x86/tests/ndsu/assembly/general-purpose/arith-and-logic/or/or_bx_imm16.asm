        ;; 16-bit OR instruction: OR BX, imm16
        ;; Encoding: 66 81 /1 iw (66 81 CB 2C 01)  [5 bytes]
        ;; Immediate 300 requires the full 16-bit form (81 /1 iw).

        global _start

        section .text
_start:
        or      bx, 300
        ret
