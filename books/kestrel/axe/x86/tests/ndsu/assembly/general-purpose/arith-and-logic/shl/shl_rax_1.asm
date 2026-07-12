        ;; 64-bit SHL register by 1: SHL RAX, 1 -- Encoding: REX.W D1 /4
        global _start

        section .text
_start:
        shl     rax, 1
        ret
