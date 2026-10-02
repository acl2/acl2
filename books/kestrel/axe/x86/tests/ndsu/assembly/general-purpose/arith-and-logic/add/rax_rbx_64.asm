        ;; 64-bit ADD instruction: ADD RAX, RBX
        ;; Encoding: REX.W + 01 /r  (48 01 D8)
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        add     rax, rbx
        ret
