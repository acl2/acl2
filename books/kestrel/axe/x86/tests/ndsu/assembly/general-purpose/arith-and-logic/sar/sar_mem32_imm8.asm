        ;; 32-bit SAR memory by imm8: SAR dword [RBX], 3 -- Encoding: C1 /7 ib
        global _start

        section .text
_start:
        sar     dword [rbx], 3
        ret
