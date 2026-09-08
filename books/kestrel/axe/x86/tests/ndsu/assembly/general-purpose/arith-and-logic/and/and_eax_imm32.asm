        ;; 32-bit AND instruction: AND EAX, imm32
        ;; Encoding: 25 id (25 E8 03 00 00)  [5 bytes]

        global _start

        section .text
_start:
        and     eax, 1000
        ret
