        ;; 64-bit OR instruction: OR RAX, RBX
        ;; Encoding: REX.W + 09 /r (48 09 D8)  [3 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        or      rax, rbx
        ret
