        ;; MOVSW: Move word from [RSI] to [RDI]
        ;; CLD clears DF so the copy direction is forward (DF=0).
        ;; Encoding: FC (cld) 66 A5 (movsw) C3 (ret) = 4 bytes; stop PC
        ;; after the first 3 bytes (before ret) = 0x401003.
        global _start

        section .text
_start:
        cld
        movsw
        ret
