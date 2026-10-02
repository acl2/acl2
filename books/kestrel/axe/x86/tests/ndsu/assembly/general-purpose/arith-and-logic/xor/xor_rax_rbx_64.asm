        ;; 64-bit XOR instruction: XOR RAX, RBX
        ;; Encoding: REX.W + 31 /r (48 31 D8)  [3 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        xor     rax, rbx
        ret
