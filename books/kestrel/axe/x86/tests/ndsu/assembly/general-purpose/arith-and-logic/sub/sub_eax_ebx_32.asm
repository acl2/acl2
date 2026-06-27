        ;; 32-bit SUB instruction: SUB EAX, EBX
        ;; Encoding: 29 /r (29 D8)  [2 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        sub     eax, ebx
        ret
