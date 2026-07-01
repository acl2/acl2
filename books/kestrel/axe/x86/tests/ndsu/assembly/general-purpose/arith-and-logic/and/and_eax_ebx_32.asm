        ;; 32-bit AND instruction: AND EAX, EBX
        ;; Encoding: 21 /r (21 D8)  [2 bytes]

        global _start

        section .text
_start:
        and     eax, ebx
        ret
