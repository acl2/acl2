        ;; 16-bit SAR register by 1: SAR AX, 1 -- Encoding: 66 D1 /7
        global _start

        section .text
_start:
        sar     ax, 1
        ret
