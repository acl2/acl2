        ;; 8-bit extended SAR memory by CL: SAR byte [R8], CL -- Encoding: REX D2 /7
        global _start

        section .text
_start:
        sar     byte [r8], cl
        ret
