        ;; 32-bit destination, 16-bit register source: CRC32 EAX, BX
        ;; Encoding: 66 F2 0F 38 F1 /r (66 F2 0F 38 F1 C3)  [6 bytes]
        global _start

        section .text
_start:
        crc32   eax, bx
        ret
