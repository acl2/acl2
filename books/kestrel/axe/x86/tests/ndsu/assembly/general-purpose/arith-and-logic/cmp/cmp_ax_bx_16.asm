        ;; 16-bit CMP instruction: CMP AX, BX
        ;; Encoding: 66 39 /r (66 39 D8)  [3 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        cmp     ax, bx
        ret
