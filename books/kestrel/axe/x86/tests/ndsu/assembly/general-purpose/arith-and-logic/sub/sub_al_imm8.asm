        ;; 8-bit SUB instruction: SUB AL, imm8
        ;; Encoding: 2C ib (2C 05)  [2 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        sub     al, 5
        ret
