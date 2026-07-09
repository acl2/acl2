        ;; 32-bit CMP instruction: CMP EAX, EBX
        ;; Encoding: 39 /r (39 D8)  [2 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        cmp     eax, ebx
        ret
