        ;; 16-bit SAR memory by 1: SAR word [RBX], 1 -- Encoding: 66 D1 /7
        global _start

        section .text
_start:
        sar     word [rbx], 1
        ret
