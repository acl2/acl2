        ;; 64-bit SAL register by CL: SAL RAX, CL -- Encoding: REX.W D3 /4
        global _start

        section .text
_start:
        sal     rax, cl
        ret
