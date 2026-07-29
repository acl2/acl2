        ;; 64-bit XOR instruction: XOR RBX, imm32
        ;; Encoding: REX.W + 81 /6 id (48 81 F3 E8 03 00 00)  [7 bytes]
        ;; The immediate 1000 is sign-extended to 64 bits; since 0 < 1000 < 2^31, value is unchanged.

        global _start

        section .text
_start:
        xor     rbx, 1000
        ret
