        ;; 32-bit SAR register by imm8: SAR EAX, 3 -- Encoding: C1 /7 ib
        global _start

        section .text
_start:
        sar     eax, 3
        ret
