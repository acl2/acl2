        ;; 32-bit SUB with sign-extended imm8: SUB [RBX], imm8 (sign-extended to 32 bits)
        ;; Encoding: 83 /5 ib = 83 2B 05  [3 bytes]

        global _start

        section .text
_start:
        sub     dword [rbx], 5
