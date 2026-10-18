        ;; 64-bit destination, 64-bit register source: CRC32 RAX, RBX
        ;; Encoding: F2 REX.W 0F 38 F1 /r (F2 48 0F 38 F1 C3)  [6 bytes]
        global _start

        section .text
_start:
        crc32   rax, rbx
        ret
