        ;; 8-bit ADD immediate to memory: ADD [RBX], imm8
        ;; Encoding: 80 /0 ib = 80 03 05  [3 bytes]

        global _start

        section .text
_start:
        add     byte [rbx], 5
