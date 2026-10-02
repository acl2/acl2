        ;; 8-bit AND instruction: AND AL, imm8
        ;; Encoding: 24 ib (24 05)  [2 bytes]

        global _start

        section .text
_start:
        and     al, 5
        ret
