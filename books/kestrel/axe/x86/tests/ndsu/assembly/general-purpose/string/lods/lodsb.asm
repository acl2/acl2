        ;; LODSB: Load byte from [RSI] into AL
        ;; CLD clears DF so RSI is incremented (DF=0).
        ;; Encoding: FC (cld) AC (lodsb) C3 (ret) = 3 bytes; stop PC after
        ;; the first 2 bytes (before ret) = 0x401002.
        global _start

        section .text
_start:
        cld
        lodsb
        ret
