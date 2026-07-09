        ;; 8-bit SHL register by CL: SHL AL, CL -- Encoding: D2 /4
        global _start

        section .text
_start:
        shl     al, cl
        ret
