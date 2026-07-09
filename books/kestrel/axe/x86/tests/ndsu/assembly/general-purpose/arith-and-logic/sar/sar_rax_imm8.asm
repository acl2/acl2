        ;; 64-bit SAR register by imm8: SAR RAX, 3 -- Encoding: REX.W C1 /7 ib
        global _start

        section .text
_start:
        sar     rax, 3
        ret
