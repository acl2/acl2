        ;; 32-bit SAL memory by CL: SAL dword [RBX], CL -- Encoding: D3 /4
        global _start

        section .text
_start:
        sal     dword [rbx], cl
        ret
