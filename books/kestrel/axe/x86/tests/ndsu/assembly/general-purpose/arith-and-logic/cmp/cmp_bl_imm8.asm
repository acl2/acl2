        ;; 8-bit CMP general register immediate: CMP BL, imm8
        ;; Encoding: 80 /7 ib = 80 FB 05  [3 bytes]

        global _start

        section .text
_start:
        cmp     bl, 5
        ret
