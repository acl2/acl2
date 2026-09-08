        ;; 8-bit AND instruction: AND BL, imm8
        ;; Encoding: 80 /4 ib (80 E3 05)  [3 bytes]

        global _start

        section .text
_start:
        and     bl, 5
        ret
