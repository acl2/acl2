        ;; 16-bit SAL memory by imm8: SAL word [RBX], 3 -- Encoding: 66 C1 /4 ib
        global _start

        section .text
_start:
        sal     word [rbx], 3
        ret
