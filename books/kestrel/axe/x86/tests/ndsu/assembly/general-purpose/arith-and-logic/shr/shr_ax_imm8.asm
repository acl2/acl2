        ;; 16-bit SHR register by imm8: SHR AX, 3 -- Encoding: 66 C1 /5 ib
        global _start

        section .text
_start:
        shr     ax, 3
        ret
