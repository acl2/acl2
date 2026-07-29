        ;; 64-bit SAL register by 1: SAL RAX, 1 -- Encoding: REX.W D1 /4
        global _start

        section .text
_start:
        sal     rax, 1
        ret
