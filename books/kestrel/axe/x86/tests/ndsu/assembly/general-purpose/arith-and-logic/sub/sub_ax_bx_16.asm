        ;; 16-bit SUB instruction: SUB AX, BX
        ;; Encoding: 66 29 /r (66 29 D8)  [3 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        sub     ax, bx
        ret
