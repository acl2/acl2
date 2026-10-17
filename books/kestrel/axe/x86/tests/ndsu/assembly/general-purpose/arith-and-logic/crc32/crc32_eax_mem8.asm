        ;; 32-bit destination, 8-bit memory source: CRC32 EAX, BYTE [RBX]
        ;; Encoding: F2 0F 38 F0 /r (F2 0F 38 F0 03)  [5 bytes]
        ;; Source operand is 1 byte read from memory at address in RBX.
        global _start

        section .text
_start:
        crc32   eax, byte [rbx]
        ret
