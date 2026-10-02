        ;; 16-bit OR instruction: OR AX, BX
        ;; Encoding: 66 09 /r (66 09 D8)  [3 bytes]

        global _start

        section .text
_start:
        or      ax, bx
        ret
