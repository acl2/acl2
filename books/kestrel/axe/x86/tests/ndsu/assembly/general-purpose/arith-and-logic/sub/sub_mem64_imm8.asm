        ;; 64-bit SUB with sign-extended imm8: SUB [RBX], imm8 (sign-extended to 64 bits)
        ;; Encoding: REX.W 83 /5 ib = 48 83 2B 05  [4 bytes]

        global _start

        section .text
_start:
        sub     qword [rbx], 5
