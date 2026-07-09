        ;; 16-bit XOR instruction: XOR AX, [RBX]
        ;; Encoding: 66 33 /r (66 33 03)  [3 bytes]
        ;; Source operand is 2 bytes (little-endian) read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        xor     ax, [rbx]
        ret
