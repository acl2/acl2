        ;; 16-bit SAR memory by CL: SAR word [RBX], CL -- Encoding: 66 D3 /7
        global _start

        section .text
_start:
        sar     word [rbx], cl
        ret
