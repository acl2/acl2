        ;; 8-bit AND instruction: AND AL, [RBX]
        ;; Encoding: 22 /r (22 03)  [2 bytes]
        ;; Source operand is 1 byte read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        and     al, [rbx]
        ret
