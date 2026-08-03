        ;; 16-bit SHR memory by 1: SHR word [RBX], 1 -- Encoding: 66 D1 /5
        global _start

        section .text
_start:
        shr     word [rbx], 1
        ret
