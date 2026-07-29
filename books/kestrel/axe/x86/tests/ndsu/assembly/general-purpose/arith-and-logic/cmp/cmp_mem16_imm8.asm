        ;; 16-bit CMP with sign-extended imm8: CMP [RBX], imm8 (sign-extended to 16 bits)
        ;; Encoding: 66 83 /7 ib = 66 83 3B 05  [4 bytes]

        global _start

        section .text
_start:
        cmp     word [rbx], 5
