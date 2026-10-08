        ;; ENTER imm16, 0  (nesting level 0)
        ;; Encoding: C8 iw 00  (C8 10 00 00 — 4 bytes; allocates 16 bytes)
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        enter   16, 0
        leave
        ret
