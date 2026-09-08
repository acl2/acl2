        ;; 8-bit OR instruction: OR AL, [RBX]
        ;; Encoding: 0A /r (0A 03)  [2 bytes]
        ;; Source operand is 1 byte read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        or      al, [rbx]
        ret
