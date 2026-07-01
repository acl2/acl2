        ;; 8-bit OR instruction: OR BL, imm8
        ;; Encoding: 80 /1 ib (80 CB 05)  [3 bytes]

        global _start

        section .text
_start:
        or      bl, 5
        ret
