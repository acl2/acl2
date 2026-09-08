        ;; 8-bit CMP instruction: CMP AL, BL
        ;; Encoding: 38 /r (38 D8)  [2 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        cmp     al, bl
        ret
