        ;; 8-bit OR immediate to memory: OR [RBX], imm8
        ;; Encoding: 80 /1 ib = 80 0B 05  [3 bytes]

        global _start

        section .text
_start:
        or      byte [rbx], 5
