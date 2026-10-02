        ;; 8-bit SHR memory by imm8: SHR byte [RBX], 3 -- Encoding: C0 /5 ib
        global _start

        section .text
_start:
        shr     byte [rbx], 3
        ret
