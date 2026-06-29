        ;; 8-bit ADD instruction: ADD BL, imm8
        ;; Encoding: 80 /0 ib = 80 C3 05  [3 bytes]

        global _start

        section .text
_start:
        add     bl, 5
        ret
