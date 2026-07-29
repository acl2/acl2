        ;; 16-bit SHL register by CL: SHL AX, CL -- Encoding: 66 D3 /4
        global _start

        section .text
_start:
        shl     ax, cl
        ret
