        ;; 32-bit SAR register by CL: SAR EAX, CL -- Encoding: D3 /7
        global _start

        section .text
_start:
        sar     eax, cl
        ret
