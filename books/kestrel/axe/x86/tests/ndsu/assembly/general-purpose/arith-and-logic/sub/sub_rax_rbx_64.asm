        ;; 64-bit SUB instruction: SUB RAX, RBX
        ;; Encoding: REX.W 29 /r (48 29 D8)  [3 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        sub     rax, rbx
        ret
