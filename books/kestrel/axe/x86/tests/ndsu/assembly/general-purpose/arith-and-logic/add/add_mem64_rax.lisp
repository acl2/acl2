; Proofs about a 1-instruction binary that adds RAX to a memory qword (64-bit reg-to-mem)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of add_mem64_rax.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "add_mem64_rax.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function add_mem64_rax, which
;; represents the effect of the program on the x86 state.
;; ADD [RBX], RAX is encoded as 48 01 03 (3 bytes), so stop PC = 0x401003.
;; Both the base address and +7 must be canonical for the 64-bit write.
(def-unrolled add_mem64_rax
  :executable "add_mem64_rax.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The qword at memory address [RBX] is updated to the 64-bit sum of the original
;; qword at [RBX] and RAX (Intel SDM Vol 2A: DEST <- DEST + SRC, size = qword).
(defthm add_mem64_rax-memory-at-rbx
  (equal (read 8 (rbx x86) (add_mem64_rax x86))
         (bvplus 64 (read 8 (rbx x86) x86) (rax x86))))

;; All other memory bytes are unchanged (only the 8 bytes at [RBX]..[RBX+7] are
;; written).
;; Condition: address is not within the 8-byte region starting at [RBX].
(defthm add_mem64_rax-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 8))
           (equal (read 1 address (add_mem64_rax x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (ADD [RBX], RAX is 3 bytes: REX.W 01 03 = 48 01 03)
(defthm add_mem64_rax-rip
  (equal (rip (add_mem64_rax x86))
         (+ 3 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm add_mem64_rax-registers
  (equal (rgfi reg (add_mem64_rax x86))
         (rgfi reg x86)))

;; The carry flag is 1 iff the 64-bit unsigned sum overflows (i.e., >= 2^64):
(defthm add_mem64_rax-cf
  (equal (get-flag :cf (add_mem64_rax x86))
         (if (<= (expt 2 64)
                 (+ (bvchop 64 (read 8 (rbx x86) x86)) (bvchop 64 (rax x86))))
             1
           0))
  :hints (("Goal" :in-theory (enable acl2::getbit-of-+-new acl2::getbit-too-high))))

;; The zero flag is 1 iff the sum, chopped down to 64 bits, is 0
(defthm add_mem64_rax-zf
  (equal (get-flag :zf (add_mem64_rax x86))
         (if (equal 0 (bvplus 64 (read 8 (rbx x86) x86) (rax x86)))
             1
           0)))

;; The sign flag is the sign bit (bit 63) of the 64-bit result.
(defthm add_mem64_rax-sf
  (equal (get-flag :sf (add_mem64_rax x86))
         (let ((sum (bvplus 64 (read 8 (rbx x86) x86) (rax x86))))
           (getbit 63 sum)))
  :hints (("Goal" :in-theory (enable bvplus))))

;; The auxiliary carry flag is 1 iff there is a carry from bit 3 into bit 4
;; (that is, the sum of the two low nibbles is greater than 15):
(defthm add_mem64_rax-af
  (equal (get-flag :af (add_mem64_rax x86))
         (if (> (+ (bvchop 4 (read 8 (rbx x86) x86))
                   (bvchop 4 (rax x86)))
                15)
             1
           0))
  :hints (("Goal" :in-theory (enable bvplus bvlt))))

;; The overflow flag is 1 iff the signed 64-bit result overflows
(defthm add_mem64_rax-of
  (equal (get-flag :of (add_mem64_rax x86))
         (let ((sum (+ (logext 64 (read 8 (rbx x86) x86))
                       (logext 64 (rax x86)))))
           (if (or (< sum (- (expt 2 63))) ; sum too small
                   (<= (expt 2 63) sum)    ; sum too big
                   )
               1 ; overflow
             0   ; no overflow
             )))
  :hints (("Goal" :in-theory (enable of-spec64 signed-byte-p))))

(local (defthm pf-spec64-alt-def
  (equal (pf-spec64 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm add_mem64_rax-pf
  (equal (get-flag :pf (add_mem64_rax x86))
         (let ((sum (+ (read 8 (rbx x86) x86) (rax x86))))
           (if (evenp (bvcount 8 sum))
               1
             0)))
  :hints (("Goal" :in-theory (enable pf-spec64-alt-def bvplus))))

(defthm add_mem64_rax-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (add_mem64_rax x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
