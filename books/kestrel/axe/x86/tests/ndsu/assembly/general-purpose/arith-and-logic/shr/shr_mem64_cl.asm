        ;; 64-bit SHR memory by CL: SHR qword [RBX], CL -- Encoding: REX.W D3 /5
        global _start

        section .text
_start:
        shr     qword [rbx], cl
        ret
