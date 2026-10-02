        ;; 16-bit AND instruction: AND AX, [RBX]
        ;; Encoding: 66 23 /r (66 23 03)  [3 bytes]
        ;; Source operand is 2 bytes (little-endian) read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        and     ax, [rbx]
        ret
