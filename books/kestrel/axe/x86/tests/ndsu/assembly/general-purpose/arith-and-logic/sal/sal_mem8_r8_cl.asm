        ;; 8-bit extended SAL memory by CL: SAL byte [R8], CL -- Encoding: REX D2 /4
        global _start

        section .text
_start:
        sal     byte [r8], cl
        ret
