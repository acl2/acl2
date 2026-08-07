        ;; 64-bit LEAVE instruction
        ;; Encoding: C9 (1 byte)
        ;; Entry point _start at 0x401000 (Linux ELF64 default)
        ;; push rbp / mov rbp, rsp set up a stack frame so that LEAVE has a
        ;; well-defined old RBP to restore from.

        global _start

        section .text
_start:
        push    rbp
        mov     rbp, rsp
        leave
        ret
