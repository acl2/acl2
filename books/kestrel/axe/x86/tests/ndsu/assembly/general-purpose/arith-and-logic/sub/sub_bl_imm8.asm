        ;; 8-bit SUB general register immediate: SUB BL, imm8
        ;; Encoding: 80 /5 ib = 80 EB 05  [3 bytes]

        global _start

        section .text
_start:
        sub     bl, 5
        ret
