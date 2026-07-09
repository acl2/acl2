        ;; 8-bit SHL register by 1: SHL AL, 1 -- Encoding: D0 /4
        global _start

        section .text
_start:
        shl     al, 1
        ret
