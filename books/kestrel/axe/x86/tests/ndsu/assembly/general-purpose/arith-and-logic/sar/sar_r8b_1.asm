        ;; 8-bit extended SAR register by 1: SAR R8B, 1 -- Encoding: REX D0 /7
        global _start

        section .text
_start:
        sar     r8b, 1
        ret
