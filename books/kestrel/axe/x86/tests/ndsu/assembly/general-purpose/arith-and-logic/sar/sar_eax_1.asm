        ;; 32-bit SAR register by 1: SAR EAX, 1 -- Encoding: D1 /7
        global _start

        section .text
_start:
        sar     eax, 1
        ret
