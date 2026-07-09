        ;; 64-bit SHL memory by 1: SHL qword [RBX], 1 -- Encoding: REX.W D1 /4
        global _start

        section .text
_start:
        shl     qword [rbx], 1
        ret
