        ;; 8-bit extended SAL register by imm8: SAL R8B, 3 -- Encoding: REX C0 /4 ib
        global _start

        section .text
_start:
        sal     r8b, 3
        ret
