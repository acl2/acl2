        ;; 8-bit extended SHL memory by imm8: SHL byte [R8], 3 -- Encoding: REX C0 /4 ib
        global _start

        section .text
_start:
        shl     byte [r8], 3
        ret
