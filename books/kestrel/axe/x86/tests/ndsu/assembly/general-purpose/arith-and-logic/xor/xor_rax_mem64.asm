        ;; 64-bit XOR instruction: XOR RAX, [RBX]
        ;; Encoding: REX.W + 33 /r (48 33 03)  [3 bytes]
        ;; Source operand is 8 bytes read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        xor     rax, [rbx]
        ret
