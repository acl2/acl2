        ;; 32-bit CMP instruction: CMP EAX, [RBX]
        ;; Encoding: 3B /r (3B 03)  [2 bytes]
        ;; Source operand is 4 bytes read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        cmp     eax, [rbx]
        ret
