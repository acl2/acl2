        ;; 32-bit CMP general register immediate: CMP EBX, imm32
        ;; Encoding: 81 /7 id = 81 FB E8 03 00 00  [6 bytes]

        global _start

        section .text
_start:
        cmp     ebx, 1000
        ret
