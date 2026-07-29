        ;; 32-bit SAL register by CL: SAL EAX, CL -- Encoding: D3 /4
        global _start

        section .text
_start:
        sal     eax, cl
        ret
