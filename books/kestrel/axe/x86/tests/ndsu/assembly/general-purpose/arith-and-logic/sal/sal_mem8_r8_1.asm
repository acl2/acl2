        ;; 8-bit extended SAL memory by 1: SAL byte [R8], 1 -- Encoding: REX D0 /4
        global _start

        section .text
_start:
        sal     byte [r8], 1
        ret
