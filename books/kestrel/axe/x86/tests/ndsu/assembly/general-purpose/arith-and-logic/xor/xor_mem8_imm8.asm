        ;; 8-bit XOR immediate to memory: XOR [RBX], imm8
        ;; Encoding: 80 /6 ib = 80 33 05  [3 bytes]

        global _start

        section .text
_start:
        xor     byte [rbx], 5
