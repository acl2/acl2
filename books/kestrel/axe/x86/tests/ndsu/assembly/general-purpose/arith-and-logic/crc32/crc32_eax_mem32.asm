        ;; 32-bit destination, 32-bit memory source: CRC32 EAX, DWORD [RBX]
        ;; Encoding: F2 0F 38 F1 /r (F2 0F 38 F1 03)  [5 bytes]
        ;; Source operand is 4 bytes read from memory at address in RBX.
        global _start

        section .text
_start:
        crc32   eax, dword [rbx]
        ret
