        ;; 32-bit SHR register by 1: SHR EAX, 1 -- Encoding: D1 /5
        global _start

        section .text
_start:
        shr     eax, 1
        ret
