        ;; ENTER imm16, imm8  (nesting level 2, as a concrete example of N > 1)
        ;; Encoding: C8 iw ib  (C8 10 00 02 — 4 bytes; allocates 16 bytes)
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        enter   16, 2
        leave
        ret
