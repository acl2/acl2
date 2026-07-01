        ;; 64-bit OR with sign-extended 8-bit immediate: OR [RBX], imm8
        ;; Encoding: REX.W + 83 /1 ib = 48 83 0B 05  [4 bytes]
        ;; The immediate 5 is sign-extended from 8 to 64 bits; since 5 > 0 and 5 < 128, value is 5.

        global _start

        section .text
_start:
        or      qword [rbx], 5
