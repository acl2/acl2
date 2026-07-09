        ;; 8-bit extended SHL memory by 1: SHL byte [R8], 1 -- Encoding: REX D0 /4
        global _start

        section .text
_start:
        shl     byte [r8], 1
        ret
