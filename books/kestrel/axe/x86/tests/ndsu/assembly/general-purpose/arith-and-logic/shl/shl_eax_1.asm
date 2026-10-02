        ;; 32-bit SHL register by 1: SHL EAX, 1 -- Encoding: D1 /4
        global _start

        section .text
_start:
        shl     eax, 1
        ret
