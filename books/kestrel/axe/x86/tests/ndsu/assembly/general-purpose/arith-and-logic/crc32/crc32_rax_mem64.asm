        ;; 64-bit destination, 64-bit memory source: CRC32 RAX, QWORD [RBX]
        ;; Encoding: F2 REX.W 0F 38 F1 /r (F2 48 0F 38 F1 03)  [6 bytes]
        ;; Source operand is 8 bytes read from memory at address in RBX.
        global _start

        section .text
_start:
        crc32   rax, qword [rbx]
        ret
