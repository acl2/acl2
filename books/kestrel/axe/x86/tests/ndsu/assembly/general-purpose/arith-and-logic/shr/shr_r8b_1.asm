        ;; 8-bit extended SHR register by 1: SHR R8B, 1 -- Encoding: REX D0 /5
        global _start

        section .text
_start:
        shr     r8b, 1
        ret
