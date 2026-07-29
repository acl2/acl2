        ;; 32-bit SHL memory by 1: SHL dword [RBX], 1 -- Encoding: D1 /4
        global _start

        section .text
_start:
        shl     dword [rbx], 1
        ret
