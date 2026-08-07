        ;; 16-bit LEAVE instruction, via the 66H operand-size-override
        ;; prefix (66 C9), executed in 64-bit (long) mode.
        ;; Entry point _start at 0x401000 (Linux ELF64 default)
        ;; push bp / mov bp, sp set up a 16-bit-sized old-BP value on the
        ;; stack so that LEAVE has a well-defined value to restore from.

        global _start

        section .text
_start:
        push    bp
        mov     bp, sp
        db      0x66              ; operand-size override prefix
        db      0xC9              ; LEAVE
        ret
