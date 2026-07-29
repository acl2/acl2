        ;; 32-bit NOT instruction: NOT EBX
        ;; Encoding: F7 /2 (F7 D3)  [2 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        not     ebx
        ret
