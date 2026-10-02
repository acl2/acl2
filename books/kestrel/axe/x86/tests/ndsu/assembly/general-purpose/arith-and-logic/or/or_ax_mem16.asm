        ;; 16-bit OR instruction: OR AX, [RBX]
        ;; Encoding: 66 0B /r (66 0B 03)  [3 bytes]
        ;; Source operand is 2 bytes (little-endian) read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        or      ax, [rbx]
        ret
