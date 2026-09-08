        ;; 32-bit SAR memory by CL: SAR dword [RBX], CL -- Encoding: D3 /7
        global _start

        section .text
_start:
        sar     dword [rbx], cl
        ret
