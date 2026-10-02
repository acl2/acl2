        ;; 8-bit extended SHL register by CL: SHL R8B, CL -- Encoding: REX D2 /4
        global _start

        section .text
_start:
        shl     r8b, cl
        ret
