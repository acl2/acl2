        ;; 64-bit ADD instruction: ADD RAX, imm32 (sign-extended to 64 bits)
        ;; Encoding: REX.W + 05 id (48 05 F4 01 00 00)  [6 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        add     rax, 500
        ret
