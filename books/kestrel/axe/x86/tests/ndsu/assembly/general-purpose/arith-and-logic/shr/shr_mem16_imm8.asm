        ;; 16-bit SHR memory by imm8: SHR word [RBX], 3 -- Encoding: 66 C1 /5 ib
        global _start

        section .text
_start:
        shr     word [rbx], 3
        ret
