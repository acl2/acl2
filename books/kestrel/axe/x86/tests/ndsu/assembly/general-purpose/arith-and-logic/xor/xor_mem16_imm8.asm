        ;; 16-bit XOR with sign-extended 8-bit immediate: XOR [RBX], imm8
        ;; Encoding: 66 83 /6 ib = 66 83 33 05  [4 bytes]
        ;; The immediate 5 fits in signed 8 bits; sign-extension to 16 bits gives 5.

        global _start

        section .text
_start:
        xor     word [rbx], 5
