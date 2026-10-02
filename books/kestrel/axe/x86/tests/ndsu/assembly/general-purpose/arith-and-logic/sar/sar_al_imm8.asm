        ;; 8-bit SAR register by imm8: SAR AL, 3 -- Encoding: C0 /7 ib
        global _start

        section .text
_start:
        sar     al, 3
        ret
