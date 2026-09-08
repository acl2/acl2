        ;; 16-bit SAL memory by 1: SAL word [RBX], 1 -- Encoding: 66 D1 /4
        global _start

        section .text
_start:
        sal     word [rbx], 1
        ret
