        ;; 64-bit ADD instruction: ADD RBX, imm32 (sign-extended)
        ;; Encoding: REX.W 81 /0 id = 48 81 C3 E8 03 00 00  [7 bytes]

        global _start

        section .text
_start:
        add     rbx, 1000
        ret
