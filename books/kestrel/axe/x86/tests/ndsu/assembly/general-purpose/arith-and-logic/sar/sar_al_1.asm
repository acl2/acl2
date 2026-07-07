        ;; 8-bit SAR register by 1: SAR AL, 1 -- Encoding: D0 /7
        global _start

        section .text
_start:
        sar     al, 1
        ret
