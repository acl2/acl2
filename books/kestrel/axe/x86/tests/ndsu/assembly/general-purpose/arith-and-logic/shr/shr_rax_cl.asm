        ;; 64-bit SHR register by CL: SHR RAX, CL -- Encoding: REX.W D3 /5
        global _start

        section .text
_start:
        shr     rax, cl
        ret
