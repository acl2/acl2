        ;; REP MOVSD with RCX=4: copy 4 dwords (16 bytes) from [RSI] to [RDI]
        ;; CLD clears DF so the copy direction is forward (DF=0).
        global _start
        section .text
_start:
            cld
            mov rcx, 4        ; concrete count
            rep movsd         ; copy 4 dwords
            ret
