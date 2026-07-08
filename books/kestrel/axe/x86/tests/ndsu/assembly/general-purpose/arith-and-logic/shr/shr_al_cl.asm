        ;; 8-bit SHR register by CL: SHR AL, CL -- Encoding: D2 /5
        global _start

        section .text
_start:
        shr     al, cl
        ret
