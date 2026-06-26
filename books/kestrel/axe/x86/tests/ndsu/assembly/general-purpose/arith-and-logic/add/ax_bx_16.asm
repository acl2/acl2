        ;; 16-bit ADD instruction: ADD AX, BX
        ;; Encoding: 66 01 /r (66 01 D8)  [3 bytes]
        ;; written by Claude

        global _start

        section .text
_start:
        add     ax, bx
        ret
