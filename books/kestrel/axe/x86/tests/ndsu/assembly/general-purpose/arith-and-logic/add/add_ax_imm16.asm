        ;; 16-bit ADD instruction: ADD AX, imm16
        ;; Encoding: 66 05 iw (66 05 F4 01)  [4 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        add     ax, 500
        ret
