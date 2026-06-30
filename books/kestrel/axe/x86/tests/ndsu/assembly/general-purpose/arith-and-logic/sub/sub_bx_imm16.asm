        ;; 16-bit SUB general register immediate: SUB BX, imm16
        ;; Encoding: 66 81 /5 iw = 66 81 EB 2C 01  [5 bytes]
        ;; (value 300 forces the 16-bit immediate form rather than sign-extended imm8)

        global _start

        section .text
_start:
        sub     bx, 300
        ret
