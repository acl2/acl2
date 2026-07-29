        ;; 8-bit extended SAR memory by imm8: SAR byte [R8], 3 -- Encoding: REX C0 /7 ib
        global _start

        section .text
_start:
        sar     byte [r8], 3
        ret
