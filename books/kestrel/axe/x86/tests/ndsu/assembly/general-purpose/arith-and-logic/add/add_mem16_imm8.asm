        ;; 16-bit ADD with sign-extended 8-bit immediate: ADD [RBX], imm8
        ;; Encoding: 66 83 /0 ib = 66 83 03 05  [4 bytes]
        ;; The immediate 5 fits in signed 8 bits; NASM uses the short form.

        global _start

        section .text
_start:
        add     word [rbx], 5
