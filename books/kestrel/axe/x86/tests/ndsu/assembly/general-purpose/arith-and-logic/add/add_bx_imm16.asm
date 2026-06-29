        ;; 16-bit ADD instruction: ADD BX, imm16
        ;; Encoding: 66 83 /0 ib = 66 83 C3 64  [4 bytes] (100 fits in imm8)

        global _start

        section .text
_start:
        add     bx, 100
        ret
