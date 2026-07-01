        ;; 16-bit AND instruction: AND AX, imm16
        ;; Encoding: 66 25 iw (66 25 2C 01)  [4 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        and     ax, 300
        ret
