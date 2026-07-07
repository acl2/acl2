        ;; 8-bit SHL memory by CL: SHL byte [RBX], CL -- Encoding: D2 /4
        global _start

        section .text
_start:
        shl     byte [rbx], cl
        ret
