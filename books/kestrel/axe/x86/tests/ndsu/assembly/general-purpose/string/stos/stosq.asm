        ;; STOSQ: Store RAX into [RDI]
        ;; CLD clears DF so RDI is incremented (DF=0).
        ;; Encoding: FC (cld) 48 AB (stosq) C3 (ret) = 4 bytes; stop PC after
        ;; the first 3 bytes (before ret) = 0x401003.
        global _start

        section .text
_start:
        cld
        stosq
        ret
