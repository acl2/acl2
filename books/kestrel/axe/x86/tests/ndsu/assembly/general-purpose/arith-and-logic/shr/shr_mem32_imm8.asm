        ;; 32-bit SHR memory by imm8: SHR dword [RBX], 3 -- Encoding: C1 /5 ib
        global _start

        section .text
_start:
        shr     dword [rbx], 3
        ret
