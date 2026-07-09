        ;; 8-bit SAL register by 1: SAL AL, 1 -- Encoding: D0 /4
        global _start

        section .text
_start:
        sal     al, 1
        ret
