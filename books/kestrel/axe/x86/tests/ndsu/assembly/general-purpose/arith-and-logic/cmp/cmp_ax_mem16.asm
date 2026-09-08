        ;; 16-bit CMP instruction: CMP AX, [RBX]
        ;; Encoding: 66 3B /r (66 3B 03)  [3 bytes]
        ;; Source operand is 2 bytes read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        cmp     ax, [rbx]
        ret
