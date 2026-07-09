        ;; 8-bit SHL memory by 1: SHL byte [RBX], 1 -- Encoding: D0 /4
        global _start

        section .text
_start:
        shl     byte [rbx], 1
        ret
