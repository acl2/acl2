        ;; 8-bit SHR memory by CL: SHR byte [RBX], CL -- Encoding: D2 /5
        global _start

        section .text
_start:
        shr     byte [rbx], cl
        ret
