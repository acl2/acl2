        ;; 32-bit LEAVE instruction (ESP/EBP), in genuine 32-bit protected
        ;; mode (an i386 ELF32 executable, not a 66H-prefixed encoding in
        ;; 64-bit/long mode: LEAVE's opcode C9 carries the D64 attribute, so
        ;; in 64-bit mode its default operand size cannot be changed to 32
        ;; bits by any prefix; genuine 32-bit LEAVE only exists in 32-bit
        ;; mode).
        ;; Encoding: C9 (1 byte)
        ;; Entry point _start at 0x08049000 (Linux ELF32 default)
        ;; push ebp / mov ebp, esp set up a stack frame so that LEAVE has a
        ;; well-defined old EBP to restore from.

        global _start
        global do_leave

        section .text
_start:
        push    ebp
        mov     ebp, esp
do_leave:
        leave
        ret
