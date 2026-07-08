        ;; 8-bit extended SHL register by imm8: SHL R8B, 3 -- Encoding: REX C0 /4 ib
        global _start

        section .text
_start:
        shl     r8b, 3
        ret
