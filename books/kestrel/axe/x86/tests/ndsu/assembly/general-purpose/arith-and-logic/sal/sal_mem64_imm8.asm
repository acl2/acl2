        ;; 64-bit SAL memory by imm8: SAL qword [RBX], 3 -- Encoding: REX.W C1 /4 ib
        global _start

        section .text
_start:
        sal     qword [rbx], 3
        ret
