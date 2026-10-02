        ;; 64-bit OR instruction: OR RAX, [RBX]
        ;; Encoding: REX.W + 0B /r (48 0B 03)  [3 bytes]
        ;; Source operand is 8 bytes read from memory at address in RBX.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        or      rax, [rbx]
        ret
