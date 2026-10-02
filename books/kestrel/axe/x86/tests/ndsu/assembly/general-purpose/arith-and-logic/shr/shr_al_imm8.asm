        ;; 8-bit SHR register by imm8: SHR AL, 3 -- Encoding: C0 /5 ib
        global _start

        section .text
_start:
        shr     al, 3
        ret
