        ;; 8-bit SHR memory by 1: SHR byte [RBX], 1 -- Encoding: D0 /5
        global _start

        section .text
_start:
        shr     byte [rbx], 1
        ret
