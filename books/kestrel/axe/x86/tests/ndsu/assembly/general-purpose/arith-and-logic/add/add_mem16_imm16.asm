        ;; 16-bit ADD immediate to memory: ADD [RBX], imm16
        ;; Encoding: 66 81 /0 iw = 66 81 03 2C 01  [5 bytes] (300 requires full imm16)

        global _start

        section .text
_start:
        add     word [rbx], 300
