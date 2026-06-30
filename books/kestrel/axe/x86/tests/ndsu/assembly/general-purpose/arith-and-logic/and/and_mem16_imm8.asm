        ;; 16-bit AND with sign-extended 8-bit immediate: AND [RBX], imm8
        ;; Encoding: 66 83 /4 ib = 66 83 23 05  [4 bytes]
        ;; The immediate 5 fits in signed 8 bits; sign-extension to 16 bits gives 5.

        global _start

        section .text
_start:
        and     word [rbx], 5
