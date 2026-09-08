        ;; 64-bit AND with sign-extended 8-bit immediate: AND [RBX], imm8
        ;; Encoding: REX.W + 83 /4 ib = 48 83 23 05  [4 bytes]
        ;; The immediate 5 is sign-extended from 8 to 64 bits; since 5 > 0 and 5 < 128, value is 5.

        global _start

        section .text
_start:
        and     qword [rbx], 5
