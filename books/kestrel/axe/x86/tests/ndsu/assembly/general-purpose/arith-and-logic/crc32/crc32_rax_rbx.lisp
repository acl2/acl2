; Proofs about a 1-instruction binary that computes a CRC32 checksum
; over a 64-bit register, writing the result to a 64-bit destination
; register.
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of crc32_rax_rbx.elf64 into logic using the
;; Axe-based x86 lifter and proves various properties.

;; (depends-on "crc32_rax_rbx.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)
(include-book "crc32-manual-spec")

;; Rewrite eax to bvchop-of-rax so proofs reduce to the rax form.
(local (defthm eax-rewrite
  (equal (eax x86) (bvchop 32 (rax x86)))
  :hints (("Goal" :in-theory (enable eax rax)))))


(def-unrolled crc32_rax_rbx
  :executable "crc32_rax_rbx.elf64"
  :target #x401000
  :stop-pcs '(#x401006)
  :feature-flags (:avx :avx2 :bmi1 :bmi2 :sse :sse2 :sse3 :lahf-sahf :sse4.2)
  :extra-rules '(x86isa::three-byte-opcode-decode-and-execute
                 x86isa::compute-mandatory-prefix-for-three-byte-opcode$inline
                 x86isa::compute-mandatory-prefix-for-0f-38-three-byte-opcode$inline
                 x86isa::64-bit-compute-mandatory-prefix-for-0f-38-three-byte-opcode$inline
                 x86isa::three-byte-opcode-modr/m-p$inline
                 x86isa::64-bit-mode-0f-38-three-byte-opcode-modr/m-p
                 x86isa::first-three-byte-opcode-execute))



;; RAX contains the new CRC, in its low 32 bits; the high 32 bits of RAX
;; are zeroed.
(defthm crc32_rax_rbx-rax
  (equal (rax (crc32_rax_rbx x86))
         (spec-crc32 (eax x86) (rbx x86) 64))
  :hints (("Goal" :in-theory (enable spec-crc32-becomes-x86isa-crc32))))

;; The high 32 bits of RAX are zeroed (Intel SDM Vol 2A: CRC32, REX.W case).
(defthm crc32_rax_rbx-upper-32-bits-zero
  (equal (slice 63 32 (rax (crc32_rax_rbx x86)))
         0)
  :hints (("Goal" :use (crc32_rax_rbx-rax
                        (:instance unsigned-byte-p-32-of-spec-crc32
                                   (crc (eax x86)) (data (rbx x86)) (data-width 64)))
           :in-theory (e/d (slice) (crc32_rax_rbx-rax spec-crc32)))))

;; The RIP is advanced by 6 (CRC32 RAX, RBX is 6 bytes: F2 48 0F 38 F1 C3)
(defthm crc32_rax_rbx-rip
  (equal (rip (crc32_rax_rbx x86))
         (+ 6 #x401000)))

;; Registers other than RAX (the destination) are unchanged; in particular,
;; RBX (the source) is unchanged, since CRC32 does not modify its source.
(defthm crc32_rax_rbx-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (crc32_rax_rbx x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; No flags are affected by CRC32 (Intel SDM Vol 2A: CRC32).
(defthm crc32_rax_rbx-flags
  (implies (member-equal flag *standard-flags*)
           (equal (get-flag flag (crc32_rax_rbx x86))
                  (get-flag flag x86))))

;; All memory addresses are unchanged (CRC32 RAX, RBX has no memory operand).
(defthm crc32_rax_rbx-memory-unchanged
  (equal (memi address (crc32_rax_rbx x86))
         (memi address x86)))
