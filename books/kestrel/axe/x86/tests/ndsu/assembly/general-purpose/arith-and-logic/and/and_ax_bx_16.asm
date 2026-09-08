        ;; 16-bit AND instruction: AND AX, BX
        ;; Encoding: 66 21 /r (66 21 D8)  [3 bytes]

        global _start

        section .text
_start:
        and     ax, bx
        ret
