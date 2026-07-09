        ;; 16-bit SAL register by 1: SAL AX, 1 -- Encoding: 66 D1 /4
        global _start

        section .text
_start:
        sal     ax, 1
        ret
