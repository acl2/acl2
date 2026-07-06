        ;; 8-bit extended SAL memory by imm8: SAL byte [R8], 3 -- Encoding: REX C0 /4 ib
        global _start

        section .text
_start:
        sal     byte [r8], 3
        ret
