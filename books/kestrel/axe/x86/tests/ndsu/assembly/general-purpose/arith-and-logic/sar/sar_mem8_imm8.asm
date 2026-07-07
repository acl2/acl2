        ;; 8-bit SAR memory by imm8: SAR byte [RBX], 3 -- Encoding: C0 /7 ib
        global _start

        section .text
_start:
        sar     byte [rbx], 3
        ret
