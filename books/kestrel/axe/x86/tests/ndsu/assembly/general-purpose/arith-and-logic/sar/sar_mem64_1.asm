        ;; 64-bit SAR memory by 1: SAR qword [RBX], 1 -- Encoding: REX.W D1 /7
        global _start

        section .text
_start:
        sar     qword [rbx], 1
        ret
