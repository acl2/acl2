        ;; 32-bit CMP with sign-extended imm8: CMP [RBX], imm8 (sign-extended to 32 bits)
        ;; Encoding: 83 /7 ib = 83 3B 05  [3 bytes]

        global _start

        section .text
_start:
        cmp     dword [rbx], 5
