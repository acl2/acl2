        ;; 64-bit CMP general register immediate: CMP RBX, imm32 (sign-extended)
        ;; Encoding: REX.W 81 /7 id = 48 81 FB E8 03 00 00  [7 bytes]

        global _start

        section .text
_start:
        cmp     rbx, 1000
        ret
