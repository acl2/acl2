        ;; 32-bit OR instruction: OR EBX, imm32
        ;; Encoding: 81 /1 id (81 CB E8 03 00 00)  [6 bytes]

        global _start

        section .text
_start:
        or      ebx, 1000
        ret
