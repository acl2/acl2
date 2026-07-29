        ;; 8-bit extended SAL register by 1: SAL R8B, 1 -- Encoding: REX D0 /4
        global _start

        section .text
_start:
        sal     r8b, 1
        ret
