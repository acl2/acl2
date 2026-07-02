        ;; 8-bit XOR instruction: XOR AL, BL
        ;; Encoding: 30 /r (30 D8)  [2 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        xor     al, bl
        ret
