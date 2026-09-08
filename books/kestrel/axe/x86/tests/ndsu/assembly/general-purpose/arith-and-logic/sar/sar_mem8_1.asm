        ;; 8-bit SAR memory by 1: SAR byte [RBX], 1 -- Encoding: D0 /7
        global _start

        section .text
_start:
        sar     byte [rbx], 1
        ret
