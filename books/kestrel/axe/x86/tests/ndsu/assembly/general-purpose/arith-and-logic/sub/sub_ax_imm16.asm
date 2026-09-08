        ;; 16-bit SUB instruction: SUB AX, imm16
        ;; Encoding: 66 2D iw (66 2D 2C 01)  [4 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        sub     ax, 300
        ret
