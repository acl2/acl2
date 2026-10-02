        ;; 32-bit AND instruction: AND EAX, [RBX]
        ;; Encoding: 23 /r (23 03)  [2 bytes]
        ;; Source operand is 4 bytes read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        and     eax, [rbx]
        ret
