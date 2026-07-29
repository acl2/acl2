        ;; 32-bit SAL memory by 1: SAL dword [RBX], 1 -- Encoding: D1 /4
        global _start

        section .text
_start:
        sal     dword [rbx], 1
        ret
