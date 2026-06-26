        ;; 8-bit ADD instruction: ADD AL, imm8
        ;; Encoding: 04 ib (04 05)  [2 bytes]

        global _start

        section .text
_start:
        add     al, 5
        ret
