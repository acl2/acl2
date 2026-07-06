        ;; 8-bit SAL memory by imm8: SAL byte [RBX], 3 -- Encoding: C0 /4 ib
        global _start

        section .text
_start:
        sal     byte [rbx], 3
        ret
