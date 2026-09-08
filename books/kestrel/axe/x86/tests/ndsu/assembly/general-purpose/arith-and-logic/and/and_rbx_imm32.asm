        ;; 64-bit AND instruction: AND RBX, imm32
        ;; Encoding: REX.W + 81 /4 id (48 81 E3 E8 03 00 00)  [7 bytes]
        ;; The immediate 1000 is sign-extended to 64 bits; since 0 < 1000 < 2^31, value is unchanged.

        global _start

        section .text
_start:
        and     rbx, 1000
        ret
