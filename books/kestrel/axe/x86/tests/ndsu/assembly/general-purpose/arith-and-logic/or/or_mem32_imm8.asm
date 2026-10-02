        ;; 32-bit OR with sign-extended 8-bit immediate: OR [RBX], imm8
        ;; Encoding: 83 /1 ib = 83 0B 05  [3 bytes]
        ;; The immediate 5 is sign-extended from 8 to 32 bits; since 5 > 0 and 5 < 128, value is 5.

        global _start

        section .text
_start:
        or      dword [rbx], 5
