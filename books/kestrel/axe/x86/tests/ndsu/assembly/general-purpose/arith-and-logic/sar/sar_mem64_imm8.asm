        ;; 64-bit SAR memory by imm8: SAR qword [RBX], 3 -- Encoding: REX.W C1 /7 ib
        global _start

        section .text
_start:
        sar     qword [rbx], 3
        ret
