        ;; 64-bit OR with sign-extended 32-bit immediate: OR [RBX], imm32
        ;; Encoding: REX.W + 81 /1 id = 48 81 0B E8 03 00 00  [7 bytes]
        ;; The immediate 1000 is sign-extended to 64 bits; since 0 < 1000 < 2^31, value is unchanged.

        global _start

        section .text
_start:
        or      qword [rbx], 1000
