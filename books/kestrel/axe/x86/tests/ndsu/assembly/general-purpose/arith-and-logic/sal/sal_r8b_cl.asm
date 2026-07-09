        ;; 8-bit extended SAL register by CL: SAL R8B, CL -- Encoding: REX D2 /4
        global _start

        section .text
_start:
        sal     r8b, cl
        ret
