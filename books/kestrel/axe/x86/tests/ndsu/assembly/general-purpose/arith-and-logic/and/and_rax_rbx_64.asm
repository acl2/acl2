        ;; 64-bit AND instruction: AND RAX, RBX
        ;; Encoding: REX.W + 21 /r (48 21 D8)  [3 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        and     rax, rbx
        ret
