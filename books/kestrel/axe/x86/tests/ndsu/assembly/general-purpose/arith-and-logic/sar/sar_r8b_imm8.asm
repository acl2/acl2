        ;; 8-bit extended SAR register by imm8: SAR R8B, 3 -- Encoding: REX C0 /7 ib
        global _start

        section .text
_start:
        sar     r8b, 3
        ret
