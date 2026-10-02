        ;; 64-bit SHR memory by 1: SHR qword [RBX], 1 -- Encoding: REX.W D1 /5
        global _start

        section .text
_start:
        shr     qword [rbx], 1
        ret
