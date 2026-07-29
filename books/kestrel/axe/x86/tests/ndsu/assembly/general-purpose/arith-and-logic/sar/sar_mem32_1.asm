        ;; 32-bit SAR memory by 1: SAR dword [RBX], 1 -- Encoding: D1 /7
        global _start

        section .text
_start:
        sar     dword [rbx], 1
        ret
