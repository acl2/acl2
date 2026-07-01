        ;; 8-bit SUB instruction: SUB AL, [RBX]
        ;; Encoding: 2A /r (2A 03)  [2 bytes]
        ;; Source operand is 1 byte read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        sub     al, [rbx]
        ret
