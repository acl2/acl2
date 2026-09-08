        ;; 8-bit SAR register by CL: SAR AL, CL -- Encoding: D2 /7
        global _start

        section .text
_start:
        sar     al, cl
        ret
