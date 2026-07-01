        ;; 64-bit ADD with sign-extended 8-bit immediate: ADD [RBX], imm8
        ;; Encoding: REX.W 83 /0 ib = 48 83 03 05  [4 bytes]
        ;; The immediate 5 fits in signed 8 bits; NASM uses the short form.

        global _start

        section .text
_start:
        add     qword [rbx], 5
