        ;; 64-bit SAR register by 1: SAR RAX, 1 -- Encoding: REX.W D1 /7
        global _start

        section .text
_start:
        sar     rax, 1
        ret
