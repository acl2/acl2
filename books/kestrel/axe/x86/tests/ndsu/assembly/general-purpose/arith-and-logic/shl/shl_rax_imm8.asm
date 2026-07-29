        ;; 64-bit SHL register by imm8: SHL RAX, 3 -- Encoding: REX.W C1 /4 ib
        global _start

        section .text
_start:
        shl     rax, 3
        ret
