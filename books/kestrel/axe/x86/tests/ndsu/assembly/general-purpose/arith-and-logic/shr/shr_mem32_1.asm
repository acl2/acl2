        ;; 32-bit SHR memory by 1: SHR dword [RBX], 1 -- Encoding: D1 /5
        global _start

        section .text
_start:
        shr     dword [rbx], 1
        ret
