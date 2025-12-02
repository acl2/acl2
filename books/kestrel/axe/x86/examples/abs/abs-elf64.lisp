; Test case for lifting a binary that calls abs()
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: in progress
;;
;; This example tests Axe's ability to:
;; 1. Detect that a call instruction targets the PLT
;; 2. Resolve the PLT entry to the symbol name "abs"
;; 3. Apply a summary for the abs() function
;;
;; The abs() function is ideal for testing because:
;; - It's a real function call (not inlined) when compiled with -O0 -fno-builtin
;; - No loops, no syscalls - pure computation
;; - Simple semantics: abs(x) = (x < 0) ? -x : x

;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

; (depends-on "abs.elf64")

;; Lift the test_abs subroutine into logic:
; Not currently working
;(def-unrolled test-abs
;    :executable "abs.elf64"
;    :target "test_abs"
;    :inputs ((x u32))  ; 32-bit input (treated as unsigned by Axe)
;    :output :rax
;    :stack-slots 10)

;; NOTE: if you execute this def-unrolled, the lifting fails at address 0x404000 (the GOT entry for abs):
;;
;;  (READ '8 '4210688 X86)   ; 4210688 = 0x404000
;;
;;  Looking at the binary:
;;  <abs@plt>:
;;    401030:  jmp *0x2fca(%rip)   # 404000 <abs@GLIBC_2.2.5>
;;
;;  Axe tried to follow the indirect jump through the GOT, but the GOT contents
;;  are unknown at static analysis time. This is the exact point where Axe
;;  needs to:
;;
;;  1. Detect that 0x401030 is in the PLT, so that Axe can do something else
;;     instead of executing that instruction.
;;     To do that, look for section named ".plt" in the ELF section headers.
;;     E.g.  readelf -S -W abs.elf64
;;     and see
;;  [10] .plt              PROGBITS        0000000000401020 001020 000020 10  AX  0   0 16
;;     where 0000000000401020 is the address; 001020 is the file offset;
;;           000020 is the size of the .plt section, and 10 is the entry size.
;;     Since 401020 <= 401030 <= 401020+20, it is in in the PLT.
;;
;;  2. Calculate the PLT index.  (401030 - 401020) = 0x10 is the offset.
;;     Divide by the entry size (0x10 / 0x10) = 1 is the PLT index.
;;
;;  3. Look up the relocation (.rela.plt) to find the symbol index.
;;     Since PLT index 0 is a stub which is not needed in .rela.plt,
;;     we need to subtract 1 from the PLT index to get the relocation index.
;;     E.g. readelf -S -W abs.elf64
;;     shows:
;;  [ 8] .rela.plt         RELA            0000000000400468 000468 000018 18  AI  3  22  8
;;     So, what do we find at .rela.pit[0]?
;;     Each .rela.plt entry is an Elf64_Rela structure (24 bytes):
;;      typedef struct {
;;          Elf64_Addr    r_offset;   // 8 bytes - GOT slot address
;;          Elf64_Xword   r_info;     // 8 bytes - symbol index + type
;;          Elf64_Sxword  r_addend;   // 8 bytes - addend (usually 0)
;;      } Elf64_Rela;
;;  The r_info field encodes two values:
;;  - Low 32 bits: 0x00000007 = relocation type (R_X86_64_JUMP_SLOT)
;;  - High 32 bits: (r_info >> 32) = 0x00000002 = symbol index into .dynsym
;;
;; 4. Look up the symbol index into .dynsym, to find the string start index into .dynstr
;;    E.g. readelf -S -W abs.elf64
;;    shows:
;;  [ 3] .dynsym           DYNSYM          0000000000400358 000358 000060 18   A  4   1  8
;;    Since each entry is 0x18 bytes, .dynsym[2] would be at 400358+30 = 0x400388
;;    The first 4 bytes at 0x400388 are the little-endian index into .dynstr
;;    There is more detail there, like type and binding and visibility, but for this case,
;;    we just look at the first 4 bytes.
;;    In this case,
;;      readelf -x .dynsym abs.elf64
;;    shows:
;;      ...
;;      0x00400388 01000000 12000000 00000000 00000000 ................
;;    So the string start index is 1.
;;    
;; 5. Look up the string in .dynstr
;;      readelf -S -W abs.elf64
;;    shows:
;;  [ 4] .dynstr           STRTAB          00000000004003b8 0003b8 000047 00   A  0   0  1
;;    Since the string start index is 1, the string is at 0x4003b9.
;;    Let's look there:
;;      readelf -x .dynstr abs.elf64
;;    shows:
;;      Hex dump of section '.dynstr':
;;        0x004003b8 00616273 005f5f6c 6962635f 73746172 .abs.__libc_star
;;    So the string starting at 0x4003b9 to the next null is "abs"
;;
;;  6. Apply an abs summary instead of trying to execute the actual library code.


;; Once library call detection is working, the above should produce
;; something equivalent to:
;;
;; (defun test-abs (x)
;;   (if (sbvlt 32 x 0)
;;       (bvuminus 32 x)
;;     x))
;;
;; Or using abs model:
;; (defun test-abs (x)
;;   (abs-model x))

;; Correctness theorems (to be enabled once library summaries work):

;; (defthm test-abs-of-positive
;;   (implies (not (sbvlt 32 x 0))  ; x >= 0
;;            (equal (test-abs x)
;;                   (bvchop 32 x))))

;; (defthm test-abs-of-negative
;;   (implies (sbvlt 32 x 0)  ; x < 0
;;            (equal (test-abs x)
;;                   (bvuminus 32 x))))

;; (defthm test-abs-examples
;;   (and (equal (test-abs 5) 5)
;;        (equal (test-abs -5) 5)
;;        (equal (test-abs 0) 0)))
