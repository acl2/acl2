        ;; 8-bit extended SHR memory by imm8: SHR byte [R8], 3 -- Encoding: REX C0 /5 ib
        global _start

        section .text
_start:
        shr     byte [r8], 3
        ret
