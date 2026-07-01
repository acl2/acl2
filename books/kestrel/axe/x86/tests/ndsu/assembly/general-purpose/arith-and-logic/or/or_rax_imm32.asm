        ;; 64-bit OR instruction: OR RAX, imm32
        ;; Encoding: REX.W + 0D id (48 0D E8 03 00 00)  [6 bytes]
        ;; The immediate 1000 is sign-extended to 64 bits; since 0 < 1000 < 2^31,
        ;; its value is unchanged by sign extension.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        or      rax, 1000
        ret
