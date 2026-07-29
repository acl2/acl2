        ;; 16-bit SAR register by CL: SAR AX, CL -- Encoding: 66 D3 /7
        global _start

        section .text
_start:
        sar     ax, cl
        ret
