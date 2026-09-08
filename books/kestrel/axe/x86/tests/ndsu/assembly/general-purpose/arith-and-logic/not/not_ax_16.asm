        ;; 16-bit NOT instruction: NOT AX
        ;; Encoding: 66 + F7 /2 (66 F7 D0)  [3 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        not     ax
        ret
