        ;; 32-bit SHL register by CL: SHL EAX, CL -- Encoding: D3 /4
        global _start

        section .text
_start:
        shl     eax, cl
        ret
