        ;; REP MOVSQ with RCX=4: copy 4 qwords (32 bytes) from [RSI] to [RDI]
        ;; CLD clears DF so the copy direction is forward (DF=0).
        global _start
        section .text
_start:
            cld
            mov rcx, 4        ; concrete count
            rep movsq         ; copy 4 qwords
            ret
