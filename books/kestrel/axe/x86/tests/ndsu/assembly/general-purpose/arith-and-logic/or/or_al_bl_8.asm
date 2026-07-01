        ;; 8-bit OR instruction: OR AL, BL
        ;; Encoding: 08 /r (08 D8)  [2 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        or      al, bl
        ret
