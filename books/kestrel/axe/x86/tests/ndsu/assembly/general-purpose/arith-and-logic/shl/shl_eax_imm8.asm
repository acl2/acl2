        ;; 32-bit SHL register by imm8: SHL EAX, 3 -- Encoding: C1 /4 ib
        global _start

        section .text
_start:
        shl     eax, 3
        ret
