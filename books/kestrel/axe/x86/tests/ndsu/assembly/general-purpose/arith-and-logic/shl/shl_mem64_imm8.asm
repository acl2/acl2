        ;; 64-bit SHL memory by imm8: SHL qword [RBX], 3 -- Encoding: REX.W C1 /4 ib
        global _start

        section .text
_start:
        shl     qword [rbx], 3
        ret
