        ;; 32-bit ADD instruction: ADD EAX, [RBX]
        ;; Encoding: 03 /r (03 03)  [2 bytes]
        ;; Source operand is 4 bytes (little-endian) read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        add     eax, [rbx]
        ret
