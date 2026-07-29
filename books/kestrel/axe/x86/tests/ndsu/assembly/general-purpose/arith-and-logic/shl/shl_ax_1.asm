        ;; 16-bit SHL register by 1: SHL AX, 1 -- Encoding: 66 D1 /4
        global _start

        section .text
_start:
        shl     ax, 1
        ret
