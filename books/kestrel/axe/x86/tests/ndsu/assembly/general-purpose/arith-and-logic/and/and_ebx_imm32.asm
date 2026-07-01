        ;; 32-bit AND instruction: AND EBX, imm32
        ;; Encoding: 81 /4 id (81 E3 E8 03 00 00)  [6 bytes]

        global _start

        section .text
_start:
        and     ebx, 1000
        ret
