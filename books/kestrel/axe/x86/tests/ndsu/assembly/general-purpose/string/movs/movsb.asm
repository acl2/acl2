        ;; MOVSB: Move byte from [RSI] to [RDI]
        ;; CLD clears DF so the copy direction is forward (DF=0).
        ;; Encoding: FC (cld) A4 (movsb) C3 (ret) = 3 bytes; stop PC after
        ;; the first 2 bytes (before ret) = 0x401002.
        global _start

        section .text
_start:
        cld
        movsb
        ret
