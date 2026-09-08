        ;; 32-bit NOT instruction: NOT EAX
        ;; Encoding: F7 /2 (F7 D0)  [2 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        not     eax
        ret
