        ;; 16-bit SHL memory by 1: SHL word [RBX], 1 -- Encoding: 66 D1 /4
        global _start

        section .text
_start:
        shl     word [rbx], 1
        ret
