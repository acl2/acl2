        ;; 32-bit XOR instruction: XOR EAX, [RBX]
        ;; Encoding: 33 /r (33 03)  [2 bytes]
        ;; Source operand is 4 bytes read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        xor     eax, [rbx]
        ret
