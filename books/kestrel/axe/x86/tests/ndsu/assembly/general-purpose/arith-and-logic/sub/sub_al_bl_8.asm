        ;; 8-bit SUB instruction: SUB AL, BL
        ;; Encoding: 28 /r (28 D8)  [2 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        sub     al, bl
        ret
