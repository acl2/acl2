        ;; 64-bit destination, 8-bit memory source: CRC32 RAX, BYTE [RBX]
        ;; Encoding: F2 REX.W 0F 38 F0 /r (F2 48 0F 38 F0 03)  [6 bytes]
        ;; Source operand is 1 byte read from memory at address in RBX.
        global _start

        section .text
_start:
        crc32   rax, byte [rbx]
        ret
