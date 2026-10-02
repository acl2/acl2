        ;; 8-bit XOR instruction: XOR AL, [RBX]
        ;; Encoding: 32 /r (32 03)  [2 bytes]
        ;; Source operand is 1 byte read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        xor     al, [rbx]
        ret
