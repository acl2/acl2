        ;; 8-bit ADD instruction: ADD AL, [RBX]
        ;; Encoding: 02 /r (02 03)  [2 bytes]
        ;; Source operand is 1 byte read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        add     al, [rbx]
        ret
