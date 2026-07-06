        ;; 64-bit NOT instruction: NOT RBX
        ;; Encoding: REX.W + F7 /2 (48 F7 D3)  [3 bytes]
        ;; Entry point _start at 0x401000 (Linux ELF64 default)

        global _start

        section .text
_start:
        not     rbx
        ret
