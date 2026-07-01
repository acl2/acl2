        ;; 64-bit SUB instruction: SUB RAX, imm32 (sign-extended)
        ;; Encoding: REX.W 2D id (48 2D E8 03 00 00)  [6 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        sub     rax, 1000
        ret
