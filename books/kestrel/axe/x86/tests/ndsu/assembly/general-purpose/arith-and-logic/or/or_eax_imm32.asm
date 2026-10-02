        ;; 32-bit OR instruction: OR EAX, imm32
        ;; Encoding: 0D id (0D E8 03 00 00)  [5 bytes]

        global _start

        section .text
_start:
        or      eax, 1000
        ret
