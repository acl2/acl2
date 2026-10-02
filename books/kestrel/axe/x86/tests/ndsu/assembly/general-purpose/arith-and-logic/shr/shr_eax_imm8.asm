        ;; 32-bit SHR register by imm8: SHR EAX, 3 -- Encoding: C1 /5 ib
        global _start

        section .text
_start:
        shr     eax, 3
        ret
