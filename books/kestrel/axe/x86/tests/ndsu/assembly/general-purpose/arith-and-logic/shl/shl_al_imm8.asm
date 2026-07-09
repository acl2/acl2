        ;; 8-bit SHL register by imm8: SHL AL, 3 -- Encoding: C0 /4 ib
        global _start

        section .text
_start:
        shl     al, 3
        ret
