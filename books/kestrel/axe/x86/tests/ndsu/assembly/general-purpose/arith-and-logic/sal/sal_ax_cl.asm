        ;; 16-bit SAL register by CL: SAL AX, CL -- Encoding: 66 D3 /4
        global _start

        section .text
_start:
        sal     ax, cl
        ret
