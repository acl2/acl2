        ;; 8-bit OR instruction: OR AL, imm8
        ;; Encoding: 0C ib (0C 05)  [2 bytes]

        global _start

        section .text
_start:
        or      al, 5
        ret
