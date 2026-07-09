        ;; 8-bit extended SAR register by CL: SAR R8B, CL -- Encoding: REX D2 /7
        global _start

        section .text
_start:
        sar     r8b, cl
        ret
