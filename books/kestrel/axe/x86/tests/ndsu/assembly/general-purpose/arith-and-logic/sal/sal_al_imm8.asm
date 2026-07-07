        ;; 8-bit SAL register by imm8: SAL AL, 3 -- Encoding: C0 /4 ib
        global _start

        section .text
_start:
        sal     al, 3
        ret
