        ;; 8-bit extended SHR register by CL: SHR R8B, CL -- Encoding: REX D2 /5
        global _start

        section .text
_start:
        shr     r8b, cl
        ret
