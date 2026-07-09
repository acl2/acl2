        ;; 32-bit SAL register by imm8: SAL EAX, 3 -- Encoding: C1 /4 ib
        global _start

        section .text
_start:
        sal     eax, 3
        ret
