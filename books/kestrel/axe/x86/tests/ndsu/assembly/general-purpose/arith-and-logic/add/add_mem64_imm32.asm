        ;; 64-bit ADD immediate to memory: ADD [RBX], imm32 (sign-extended to 64 bits)
        ;; Encoding: REX.W 81 /0 id = 48 81 03 E8 03 00 00  [7 bytes]

        global _start

        section .text
_start:
        add     qword [rbx], 1000
