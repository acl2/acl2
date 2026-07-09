        ;; 32-bit SAL memory by imm8: SAL dword [RBX], 3 -- Encoding: C1 /4 ib
        global _start

        section .text
_start:
        sal     dword [rbx], 3
        ret
