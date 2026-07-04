        ;; 16-bit XOR immediate to memory: XOR [RBX], imm16
        ;; Encoding: 66 81 /6 iw = 66 81 33 2C 01  [5 bytes] (300 requires full imm16)

        global _start

        section .text
_start:
        xor     word [rbx], 300
