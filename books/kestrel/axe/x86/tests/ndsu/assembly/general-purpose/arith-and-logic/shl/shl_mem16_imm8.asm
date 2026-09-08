        ;; 16-bit SHL memory by imm8: SHL word [RBX], 3 -- Encoding: 66 C1 /4 ib
        global _start

        section .text
_start:
        shl     word [rbx], 3
        ret
