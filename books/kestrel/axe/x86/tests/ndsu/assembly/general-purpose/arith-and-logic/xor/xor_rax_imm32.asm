        ;; 64-bit XOR instruction: XOR RAX, imm32
        ;; Encoding: REX.W + 35 id (48 35 E8 03 00 00)  [6 bytes]
        ;; The immediate 1000 is sign-extended to 64 bits; since 0 < 1000 < 2^31,
        ;; its value is unchanged by sign extension.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        xor     rax, 1000
        ret
