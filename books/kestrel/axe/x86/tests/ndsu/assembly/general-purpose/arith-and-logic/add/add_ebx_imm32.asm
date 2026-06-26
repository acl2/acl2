        ;; 32-bit ADD instruction: ADD EBX, imm32
        ;; Encoding: 81 /0 id = 81 C3 E8 03 00 00  [6 bytes]

        global _start

        section .text
_start:
        add     ebx, 1000
        ret
