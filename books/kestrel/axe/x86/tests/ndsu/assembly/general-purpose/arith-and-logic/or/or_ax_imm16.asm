        ;; 16-bit OR instruction: OR AX, imm16
        ;; Encoding: 66 0D iw (66 0D 2C 01)  [4 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        or      ax, 300
        ret
