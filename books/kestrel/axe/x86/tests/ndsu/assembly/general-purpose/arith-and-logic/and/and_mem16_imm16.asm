        ;; 16-bit AND immediate to memory: AND [RBX], imm16
        ;; Encoding: 66 81 /4 iw = 66 81 23 2C 01  [5 bytes] (300 requires full imm16)

        global _start

        section .text
_start:
        and     word [rbx], 300
