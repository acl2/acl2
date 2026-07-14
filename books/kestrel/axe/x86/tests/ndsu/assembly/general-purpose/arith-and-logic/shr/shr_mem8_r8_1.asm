        ;; 8-bit extended SHR memory by 1: SHR byte [R8], 1 -- Encoding: REX D0 /5
        global _start

        section .text
_start:
        shr     byte [r8], 1
        ret
