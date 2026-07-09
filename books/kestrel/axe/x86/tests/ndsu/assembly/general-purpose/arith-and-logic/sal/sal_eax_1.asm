        ;; 32-bit SAL register by 1: SAL EAX, 1 -- Encoding: D1 /4
        global _start

        section .text
_start:
        sal     eax, 1
        ret
