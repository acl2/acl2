        ;; 8-bit extended SHR memory by CL: SHR byte [R8], CL -- Encoding: REX D2 /5
        global _start

        section .text
_start:
        shr     byte [r8], cl
        ret
