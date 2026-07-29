        ;; 16-bit SHR register by CL: SHR AX, CL -- Encoding: 66 D3 /5
        global _start

        section .text
_start:
        shr     ax, cl
        ret
