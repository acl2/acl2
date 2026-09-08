        ;; 32-bit SUB general register immediate: SUB EBX, imm32
        ;; Encoding: 81 /5 id = 81 EB E8 03 00 00  [6 bytes]

        global _start

        section .text
_start:
        sub     ebx, 1000
        ret
