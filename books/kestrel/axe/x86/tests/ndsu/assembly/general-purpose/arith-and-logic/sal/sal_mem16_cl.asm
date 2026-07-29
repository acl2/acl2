        ;; 16-bit SAL memory by CL: SAL word [RBX], CL -- Encoding: 66 D3 /4
        global _start

        section .text
_start:
        sal     word [rbx], cl
        ret
