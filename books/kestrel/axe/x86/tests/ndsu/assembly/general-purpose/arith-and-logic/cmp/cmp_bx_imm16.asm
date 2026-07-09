        ;; 16-bit CMP general register immediate: CMP BX, imm16
        ;; Encoding: 66 81 /7 iw = 66 81 FB 2C 01  [5 bytes]
        ;; (value 300 forces the 16-bit immediate form rather than sign-extended imm8)

        global _start

        section .text
_start:
        cmp     bx, 300
        ret
