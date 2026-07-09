        ;; 64-bit CMP instruction: CMP RAX, RBX
        ;; Encoding: REX.W 39 /r (48 39 D8)  [3 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        cmp     rax, rbx
        ret
