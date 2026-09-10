        ;; MOVSQ: Move qword from [RSI] to [RDI]
        ;; CLD clears DF so the copy direction is forward (DF=0).
        ;; Encoding: FC (cld) 48 A5 (movsq, REX.W A5) C3 (ret) = 4 bytes;
        ;; stop PC after the first 3 bytes (before ret) = 0x401003.
        global _start

        section .text
_start:
        cld
        movsq
        ret
