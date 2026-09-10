        ;; ENTER imm16, 1  (nesting level 1)
        ;; Encoding: C8 iw 01  (C8 10 00 01 — 4 bytes; allocates 16 bytes)
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        enter   16, 1
        leave
        ret
