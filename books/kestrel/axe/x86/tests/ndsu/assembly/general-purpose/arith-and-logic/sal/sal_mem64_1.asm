        ;; 64-bit SAL memory by 1: SAL qword [RBX], 1 -- Encoding: REX.W D1 /4
        global _start

        section .text
_start:
        sal     qword [rbx], 1
        ret
