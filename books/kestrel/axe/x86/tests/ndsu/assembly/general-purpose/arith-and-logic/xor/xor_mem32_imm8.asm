        ;; 32-bit XOR with sign-extended 8-bit immediate: XOR [RBX], imm8
        ;; Encoding: 83 /6 ib = 83 33 05  [3 bytes]
        ;; The immediate 5 is sign-extended from 8 to 32 bits; since 5 > 0 and 5 < 128, value is 5.

        global _start

        section .text
_start:
        xor     dword [rbx], 5
