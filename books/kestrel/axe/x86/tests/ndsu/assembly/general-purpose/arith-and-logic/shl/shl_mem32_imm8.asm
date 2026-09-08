        ;; 32-bit SHL memory by imm8: SHL dword [RBX], 3 -- Encoding: C1 /4 ib
        global _start

        section .text
_start:
        shl     dword [rbx], 3
        ret
