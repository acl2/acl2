        ;; 32-bit OR instruction: OR EAX, EBX
        ;; Encoding: 09 /r (09 D8)  [2 bytes]

        global _start

        section .text
_start:
        or      eax, ebx
        ret
