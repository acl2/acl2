        ;; 64-bit SUB instruction: SUB RAX, [RBX]
        ;; Encoding: REX.W 2B /r (48 2B 03)  [3 bytes]
        ;; Source operand is 8 bytes read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        sub     rax, [rbx]
        ret
