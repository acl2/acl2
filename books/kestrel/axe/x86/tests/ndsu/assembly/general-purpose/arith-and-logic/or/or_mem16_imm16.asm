        ;; 16-bit OR immediate to memory: OR [RBX], imm16
        ;; Encoding: 66 81 /1 iw = 66 81 0B 2C 01  [5 bytes] (300 requires full imm16)

        global _start

        section .text
_start:
        or      word [rbx], 300
