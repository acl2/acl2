        ;; 64-bit CMP instruction: CMP RAX, imm32 (sign-extended)
        ;; Encoding: REX.W 3D id (48 3D E8 03 00 00)  [6 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        cmp     rax, 1000
        ret
