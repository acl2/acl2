        ;; 64-bit SHR register by 1: SHR RAX, 1 -- Encoding: REX.W D1 /5
        global _start

        section .text
_start:
        shr     rax, 1
        ret
