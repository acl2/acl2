        ;; 8-bit CMP instruction: CMP AL, [RBX]
        ;; Encoding: 3A /r (3A 03)  [2 bytes]
        ;; Source operand is 1 byte read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        cmp     al, [rbx]
        ret
