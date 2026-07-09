        ;; 8-bit SAR memory by CL: SAR byte [RBX], CL -- Encoding: D2 /7
        global _start

        section .text
_start:
        sar     byte [rbx], cl
        ret
