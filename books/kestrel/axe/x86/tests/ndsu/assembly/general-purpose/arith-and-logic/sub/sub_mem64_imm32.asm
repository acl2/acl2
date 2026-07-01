        ;; 64-bit SUB immediate to memory: SUB [RBX], imm32 (sign-extended)
        ;; Encoding: REX.W 81 /5 id = 48 81 2B E8 03 00 00  [7 bytes]

        global _start

        section .text
_start:
        sub     qword [rbx], 1000
