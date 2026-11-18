        ;; SCASB: Compare AL with [RDI]
        ;; CLD clears DF so RDI is incremented (DF=0).
        ;; Encoding: FC (cld) AE (scasb) C3 (ret) = 3 bytes; stop PC after
        ;; the first 2 bytes (before ret) = 0x401002.
        global _start

        section .text
_start:
        cld
        scasb
        ret
