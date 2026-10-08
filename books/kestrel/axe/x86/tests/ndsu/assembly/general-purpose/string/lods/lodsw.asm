        ;; LODSW: Load word from [RSI] into AX
        ;; CLD clears DF so RSI is incremented (DF=0).
        ;; Encoding: FC (cld) 66 AD (lodsw) C3 (ret) = 4 bytes; stop PC
        ;; after the first 3 bytes (before ret) = 0x401003.
        global _start

        section .text
_start:
        cld
        lodsw
        ret
