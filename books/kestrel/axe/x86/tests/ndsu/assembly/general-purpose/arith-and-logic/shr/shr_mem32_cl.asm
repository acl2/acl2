        ;; 32-bit SHR memory by CL: SHR dword [RBX], CL -- Encoding: D3 /5
        global _start

        section .text
_start:
        shr     dword [rbx], cl
        ret
