        ;; 16-bit SHR memory by CL: SHR word [RBX], CL -- Encoding: 66 D3 /5
        global _start

        section .text
_start:
        shr     word [rbx], cl
        ret
