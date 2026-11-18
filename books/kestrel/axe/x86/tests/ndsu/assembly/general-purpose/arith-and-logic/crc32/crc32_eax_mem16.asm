        ;; 32-bit destination, 16-bit memory source: CRC32 EAX, WORD [RBX]
        ;; Encoding: 66 F2 0F 38 F1 /r (66 F2 0F 38 F1 03)  [6 bytes]
        ;; Source operand is 2 bytes read from memory at address in RBX.
        global _start

        section .text
_start:
        crc32   eax, word [rbx]
        ret
