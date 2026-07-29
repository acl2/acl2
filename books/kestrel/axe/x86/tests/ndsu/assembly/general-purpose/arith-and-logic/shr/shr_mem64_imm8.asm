        ;; 64-bit SHR memory by imm8: SHR qword [RBX], 3 -- Encoding: REX.W C1 /5 ib
        global _start

        section .text
_start:
        shr     qword [rbx], 3
        ret
