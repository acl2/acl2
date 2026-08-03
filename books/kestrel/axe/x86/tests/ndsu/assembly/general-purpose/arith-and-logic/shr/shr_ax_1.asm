        ;; 16-bit SHR register by 1: SHR AX, 1 -- Encoding: 66 D1 /5
        global _start

        section .text
_start:
        shr     ax, 1
        ret
