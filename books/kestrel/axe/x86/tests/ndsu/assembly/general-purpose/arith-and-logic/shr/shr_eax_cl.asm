        ;; 32-bit SHR register by CL: SHR EAX, CL -- Encoding: D3 /5
        global _start

        section .text
_start:
        shr     eax, cl
        ret
