        ;; 8-bit SAL memory by CL: SAL byte [RBX], CL -- Encoding: D2 /4
        global _start

        section .text
_start:
        sal     byte [rbx], cl
        ret
