        ;; 8-bit NOT instruction: NOT BL
        ;; Encoding: F6 /2 (F6 D3)  [2 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        not     bl
        ret
