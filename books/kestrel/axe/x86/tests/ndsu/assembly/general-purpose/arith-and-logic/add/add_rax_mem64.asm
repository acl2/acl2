        ;; 64-bit ADD instruction: ADD RAX, [RBX]
        ;; Encoding: REX.W + 03 /r (48 03 03)  [3 bytes]
        ;; Source operand is 8 bytes (little-endian) read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        add     rax, [rbx]
        ret
