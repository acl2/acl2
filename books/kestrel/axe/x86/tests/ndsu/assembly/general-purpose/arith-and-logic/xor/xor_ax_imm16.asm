        ;; 16-bit XOR instruction: XOR AX, imm16
        ;; Encoding: 66 35 iw (66 35 2C 01)  [4 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        xor     ax, 300
        ret
