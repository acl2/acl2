        ;; 8-bit NOT instruction: NOT AL
        ;; Encoding: F6 /2 (F6 D0)  [2 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        not     al
        ret
