        ;; 16-bit SAR memory by imm8: SAR word [RBX], 3 -- Encoding: 66 C1 /7 ib
        global _start

        section .text
_start:
        sar     word [rbx], 3
        ret
