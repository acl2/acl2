        ;; 8-bit SHR register by 1: SHR AL, 1 -- Encoding: D0 /5
        global _start

        section .text
_start:
        shr     al, 1
        ret
