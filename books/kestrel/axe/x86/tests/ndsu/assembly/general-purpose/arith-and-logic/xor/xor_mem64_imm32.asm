        ;; 64-bit XOR with sign-extended 32-bit immediate: XOR [RBX], imm32
        ;; Encoding: REX.W + 81 /6 id = 48 81 33 E8 03 00 00  [7 bytes]
        ;; The immediate 1000 is sign-extended to 64 bits; since 0 < 1000 < 2^31, value is unchanged.

        global _start

        section .text
_start:
        xor     qword [rbx], 1000
