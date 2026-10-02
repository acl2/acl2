        ;; 16-bit SUB instruction: SUB AX, [RBX]
        ;; Encoding: 66 2B /r (66 2B 03)  [3 bytes]
        ;; Source operand is 2 bytes read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        sub     ax, [rbx]
        ret
