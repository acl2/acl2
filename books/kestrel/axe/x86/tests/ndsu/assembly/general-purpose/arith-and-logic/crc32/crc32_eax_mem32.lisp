; Proofs about a 1-instruction binary that computes a CRC32 checksum
; over a dword read from memory.
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of crc32_eax_mem32.elf64 into logic using the
;; Axe-based x86 lifter and proves various properties.

;; (depends-on "crc32_eax_mem32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)
(include-book "crc32-manual-spec")

;; Rewrite eax to bvchop-of-rax so proofs reduce to the rax form.
(local (defthm eax-rewrite
  (equal (eax x86) (bvchop 32 (rax x86)))
  :hints (("Goal" :in-theory (enable eax rax)))))


(def-unrolled crc32_eax_mem32
  :executable "crc32_eax_mem32.elf64"
  :target #x401000
  :stop-pcs '(#x401005)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 3 (rbx x86))))
  :feature-flags (:avx :avx2 :bmi1 :bmi2 :sse :sse2 :sse3 :lahf-sahf :sse4.2)
  :extra-rules '(x86isa::three-byte-opcode-decode-and-execute
                 x86isa::compute-mandatory-prefix-for-three-byte-opcode$inline
                 x86isa::compute-mandatory-prefix-for-0f-38-three-byte-opcode$inline
                 x86isa::64-bit-compute-mandatory-prefix-for-0f-38-three-byte-opcode$inline
                 x86isa::three-byte-opcode-modr/m-p$inline
                 x86isa::64-bit-mode-0f-38-three-byte-opcode-modr/m-p
                 x86isa::first-three-byte-opcode-execute))



;; RAX contains the new CRC (32 bits, so the write to EAX zero-extends to RAX).
(defthm crc32_eax_mem32-rax
  (equal (rax (crc32_eax_mem32 x86))
         (spec-crc32 (eax x86) (read 4 (rbx x86) x86) 32))
  :hints (("Goal" :in-theory (enable spec-crc32-becomes-x86isa-crc32))))

;; EAX contains the new CRC (the natural statement for this instruction).
(defthm crc32_eax_mem32-eax
  (equal (eax (crc32_eax_mem32 x86))
         (spec-crc32 (eax x86) (read 4 (rbx x86) x86) 32))
  :hints (("Goal" :in-theory (enable eax spec-crc32-becomes-x86isa-crc32))))

;; The RIP is advanced by 5 (CRC32 EAX, DWORD [RBX] is 5 bytes: F2 0F 38 F1 03)
(defthm crc32_eax_mem32-rip
  (equal (rip (crc32_eax_mem32 x86))
         (+ 5 #x401000)))

;; Registers other than RAX (the destination, EAX) are unchanged.
(defthm crc32_eax_mem32-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (crc32_eax_mem32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; No flags are affected by CRC32 (Intel SDM Vol 2A: CRC32).
(defthm crc32_eax_mem32-flags
  (implies (member-equal flag *standard-flags*)
           (equal (get-flag flag (crc32_eax_mem32 x86))
                  (get-flag flag x86))))

;; All memory addresses are unchanged (instruction reads from memory but does not write).
(defthm crc32_eax_mem32-memory-unchanged
  (equal (memi address (crc32_eax_mem32 x86))
         (memi address x86)))
