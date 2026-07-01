        ;; 64-bit AND instruction: AND RAX, [RBX]
        ;; Encoding: REX.W + 23 /r (48 23 03)  [3 bytes]
        ;; Source operand is 8 bytes read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        and     rax, [rbx]
        ret
