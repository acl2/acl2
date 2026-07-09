        ;; 8-bit SAL memory by 1: SAL byte [RBX], 1 -- Encoding: D0 /4
        global _start

        section .text
_start:
        sal     byte [rbx], 1
        ret
