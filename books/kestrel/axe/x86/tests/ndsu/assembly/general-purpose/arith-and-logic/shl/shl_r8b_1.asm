        ;; 8-bit extended SHL register by 1: SHL R8B, 1 -- Encoding: REX D0 /4
        global _start

        section .text
_start:
        shl     r8b, 1
        ret
