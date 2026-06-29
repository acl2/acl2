        ;; 8-bit ADD instruction: ADD AL, BL
        ;; Encoding: 00 /r (00 D8)  [2 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        add     al, bl
        ret
