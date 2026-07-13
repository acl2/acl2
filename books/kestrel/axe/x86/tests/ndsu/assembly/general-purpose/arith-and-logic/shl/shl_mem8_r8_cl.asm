        ;; 8-bit extended SHL memory by CL: SHL byte [R8], CL -- Encoding: REX D2 /4
        global _start

        section .text
_start:
        shl     byte [r8], cl
        ret
