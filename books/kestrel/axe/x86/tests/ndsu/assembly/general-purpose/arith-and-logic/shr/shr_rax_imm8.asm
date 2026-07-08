        ;; 64-bit SHR register by imm8: SHR RAX, 3 -- Encoding: REX.W C1 /5 ib
        global _start

        section .text
_start:
        shr     rax, 3
        ret
