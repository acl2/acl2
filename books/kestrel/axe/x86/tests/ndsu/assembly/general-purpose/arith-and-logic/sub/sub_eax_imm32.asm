        ;; 32-bit SUB instruction: SUB EAX, imm32
        ;; Encoding: 2D id (2D E8 03 00 00)  [5 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        sub     eax, 1000
        ret
