        ;; 64-bit SAR register by CL: SAR RAX, CL -- Encoding: REX.W D3 /7
        global _start

        section .text
_start:
        sar     rax, cl
        ret
