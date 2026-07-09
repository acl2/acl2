        ;; 8-bit SHL memory by imm8: SHL byte [RBX], 3 -- Encoding: C0 /4 ib
        global _start

        section .text
_start:
        shl     byte [rbx], 3
        ret
