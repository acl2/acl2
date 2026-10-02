        ;; 32-bit SUB instruction: SUB EAX, [RBX]
        ;; Encoding: 2B /r (2B 03)  [2 bytes]
        ;; Source operand is 4 bytes read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        sub     eax, [rbx]
        ret
