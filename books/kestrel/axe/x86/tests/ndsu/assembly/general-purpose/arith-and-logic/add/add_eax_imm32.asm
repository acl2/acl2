        ;; 32-bit ADD instruction: ADD EAX, imm32
        ;; Encoding: 05 id (05 F4 01 00 00)  [5 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        add     eax, 500
        ret
