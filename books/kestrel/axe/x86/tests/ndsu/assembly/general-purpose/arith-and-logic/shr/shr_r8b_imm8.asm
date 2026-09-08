        ;; 8-bit extended SHR register by imm8: SHR R8B, 3 -- Encoding: REX C0 /5 ib
        global _start

        section .text
_start:
        shr     r8b, 3
        ret
