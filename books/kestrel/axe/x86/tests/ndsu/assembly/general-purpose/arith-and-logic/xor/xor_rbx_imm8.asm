        ;; 64-bit XOR instruction: XOR RBX, imm8 (sign-extended)
        ;; Encoding: REX.W + 83 /6 ib (48 83 F3 05)  [4 bytes]
        ;; The immediate 5 is sign-extended from 8 to 64 bits; since 5 > 0 and 5 < 128, value is 5.

        global _start

        section .text
_start:
        xor     rbx, 5
        ret
