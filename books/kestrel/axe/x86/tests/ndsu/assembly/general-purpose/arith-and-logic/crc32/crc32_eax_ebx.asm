        ;; 32-bit destination, 32-bit register source: CRC32 EAX, EBX
        ;; Encoding: F2 0F 38 F1 /r (F2 0F 38 F1 C3)  [5 bytes]
        global _start

        section .text
_start:
        crc32   eax, ebx
        ret
