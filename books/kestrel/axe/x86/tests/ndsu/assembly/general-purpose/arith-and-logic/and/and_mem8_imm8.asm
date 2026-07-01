        ;; 8-bit AND immediate to memory: AND [RBX], imm8
        ;; Encoding: 80 /4 ib = 80 23 05  [3 bytes]

        global _start

        section .text
_start:
        and     byte [rbx], 5
