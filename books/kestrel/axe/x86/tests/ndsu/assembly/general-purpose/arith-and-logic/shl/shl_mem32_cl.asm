        ;; 32-bit SHL memory by CL: SHL dword [RBX], CL -- Encoding: D3 /4
        global _start

        section .text
_start:
        shl     dword [rbx], cl
        ret
