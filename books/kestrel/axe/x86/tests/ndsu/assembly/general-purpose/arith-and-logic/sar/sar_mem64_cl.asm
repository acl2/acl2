        ;; 64-bit SAR memory by CL: SAR qword [RBX], CL -- Encoding: REX.W D3 /7
        global _start

        section .text
_start:
        sar     qword [rbx], cl
        ret
