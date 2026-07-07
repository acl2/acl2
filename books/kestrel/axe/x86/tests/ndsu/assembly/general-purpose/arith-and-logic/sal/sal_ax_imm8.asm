        ;; 16-bit SAL register by imm8: SAL AX, 3 -- Encoding: 66 C1 /4 ib
        global _start

        section .text
_start:
        sal     ax, 3
        ret
