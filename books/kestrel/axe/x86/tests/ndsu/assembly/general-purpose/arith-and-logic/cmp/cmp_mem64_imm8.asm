        ;; 64-bit CMP with sign-extended imm8: CMP [RBX], imm8 (sign-extended to 64 bits)
        ;; Encoding: REX.W 83 /7 ib = 48 83 3B 05  [4 bytes]

        global _start

        section .text
_start:
        cmp     qword [rbx], 5
