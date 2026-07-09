        ;; 64-bit SAL memory by CL: SAL qword [RBX], CL -- Encoding: REX.W D3 /4
        global _start

        section .text
_start:
        sal     qword [rbx], cl
        ret
