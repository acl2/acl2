        ;; 64-bit SAL register by imm8: SAL RAX, 3 -- Encoding: REX.W C1 /4 ib
        global _start

        section .text
_start:
        sal     rax, 3
        ret
