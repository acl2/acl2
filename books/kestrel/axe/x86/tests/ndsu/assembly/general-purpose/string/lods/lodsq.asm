        ;; LODSQ: Load qword from [RSI] into RAX
        ;; CLD clears DF so RSI is incremented (DF=0).
        ;; Encoding: FC (cld) 48 AD (lodsq) C3 (ret) = 4 bytes; stop PC
        ;; after the first 3 bytes (before ret) = 0x401003.
        global _start

        section .text
_start:
        cld
        lodsq
        ret
