        ;; 64-bit SUB general register immediate: SUB RBX, imm32 (sign-extended)
        ;; Encoding: REX.W 81 /5 id = 48 81 EB E8 03 00 00  [7 bytes]

        global _start

        section .text
_start:
        sub     rbx, 1000
        ret
