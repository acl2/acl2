        ;; 16-bit SAR register by imm8: SAR AX, 3 -- Encoding: 66 C1 /7 ib
        global _start

        section .text
_start:
        sar     ax, 3
        ret
