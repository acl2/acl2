        ;; 8-bit AND instruction: AND AL, BL
        ;; Encoding: 20 /r (20 D8)  [2 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        and     al, bl
        ret
