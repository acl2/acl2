        ;; 8-bit extended SAR memory by 1: SAR byte [R8], 1 -- Encoding: REX D0 /7
        global _start

        section .text
_start:
        sar     byte [r8], 1
        ret
