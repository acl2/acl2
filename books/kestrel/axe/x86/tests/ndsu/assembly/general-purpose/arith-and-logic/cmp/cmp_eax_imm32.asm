        ;; 32-bit CMP instruction: CMP EAX, imm32
        ;; Encoding: 3D id (3D E8 03 00 00)  [5 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        cmp     eax, 1000
        ret
