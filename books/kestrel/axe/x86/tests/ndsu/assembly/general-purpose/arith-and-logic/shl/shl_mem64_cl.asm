        ;; 64-bit SHL memory by CL: SHL qword [RBX], CL -- Encoding: REX.W D3 /4
        global _start

        section .text
_start:
        shl     qword [rbx], cl
        ret
