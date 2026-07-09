        ;; 8-bit CMP instruction: CMP AL, imm8
        ;; Encoding: 3C ib (3C 05)  [2 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        cmp     al, 5
        ret
