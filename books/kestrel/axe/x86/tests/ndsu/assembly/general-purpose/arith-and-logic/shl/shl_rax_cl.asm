        ;; 64-bit SHL register by CL: SHL RAX, CL -- Encoding: REX.W D3 /4
        global _start

        section .text
_start:
        shl     rax, cl
        ret
