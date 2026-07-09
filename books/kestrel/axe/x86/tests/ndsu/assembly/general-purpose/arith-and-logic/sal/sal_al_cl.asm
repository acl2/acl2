        ;; 8-bit SAL register by CL: SAL AL, CL -- Encoding: D2 /4
        global _start

        section .text
_start:
        sal     al, cl
        ret
