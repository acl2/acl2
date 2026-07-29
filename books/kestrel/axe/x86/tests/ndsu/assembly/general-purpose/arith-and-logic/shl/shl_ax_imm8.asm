        ;; 16-bit SHL register by imm8: SHL AX, 3 -- Encoding: 66 C1 /4 ib
        global _start

        section .text
_start:
        shl     ax, 3
        ret
