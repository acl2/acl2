        ;; REP MOVSW with RCX=4: copy 4 words (8 bytes) from [RSI] to [RDI]
        ;; CLD clears DF so the copy direction is forward (DF=0).
        global _start
        section .text
_start:
            cld
            mov rcx, 4        ; concrete count
            rep movsw         ; copy 4 words
            ret
