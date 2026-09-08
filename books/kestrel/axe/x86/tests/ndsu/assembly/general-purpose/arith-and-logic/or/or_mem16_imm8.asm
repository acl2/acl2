        ;; 16-bit OR with sign-extended 8-bit immediate: OR [RBX], imm8
        ;; Encoding: 66 83 /1 ib = 66 83 0B 05  [4 bytes]
        ;; The immediate 5 fits in signed 8 bits; sign-extension to 16 bits gives 5.

        global _start

        section .text
_start:
        or      word [rbx], 5
