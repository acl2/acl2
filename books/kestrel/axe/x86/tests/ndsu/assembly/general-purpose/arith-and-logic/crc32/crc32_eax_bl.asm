        global _start

        section .text
_start:
        crc32   eax, bl
        ret
