        ;; 32-bit XOR instruction: XOR EAX, EBX
        ;; Encoding: 31 /r (31 D8)  [2 bytes]

        global _start

        section .text
_start:
        xor     eax, ebx
        ret
