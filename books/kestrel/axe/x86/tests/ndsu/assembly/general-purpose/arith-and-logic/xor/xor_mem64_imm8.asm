        ;; 64-bit XOR with sign-extended 8-bit immediate: XOR [RBX], imm8
        ;; Encoding: REX.W + 83 /6 ib = 48 83 33 05  [4 bytes]
        ;; The immediate 5 is sign-extended from 8 to 64 bits; since 5 > 0 and 5 < 128, value is 5.

        global _start

        section .text
_start:
        xor     qword [rbx], 5
