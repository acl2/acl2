        ;; 16-bit CMP instruction: CMP AX, imm16
        ;; Encoding: 66 3D iw (66 3D 2C 01)  [4 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        cmp     ax, 300
        ret
