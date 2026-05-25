; Proofs about a 1-instruction binary that adds 2 numbers
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of add.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "add.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function add, which
;; represents the effect of the program on the x86 state.
(def-unrolled add
  :executable "add.elf64"
  :target #x401000
  :stop-pcs '(#x401002))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 32-bit sum of the initial RAX and  RBX
(defthm add-rax
  (equal (rax (add x86))
         (bvplus 32 (rax x86) (rbx x86))))

;; The RIP is advanced by 2
(defthm add-rip
  (equal (rip (add x86))
         (+ 2 #x401000)))

;; Registers other than RAX are unchanged.
(defthm add-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (add x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax ; todo
                                     ))))

;; The carry flag is 1 iff the sum of the 32-bit value is >= 2^32:
(defthm add-cf
  (equal (get-flag :cf (add x86))
         (if (<= (expt 2 32)
                 (+ (bvchop 32 (rax x86)) (bvchop 32 (rbx x86))))
             1
           0))
  :hints (("Goal" :in-theory (enable acl2::getbit-of-+-new))))

;; The zero flag is 1 iff the sum, chopped down to 32 bits, is 0
(defthm add-zf
  (equal (get-flag :zf (add x86))
         (if (equal 0 (bvplus 32 (rax x86) (rbx x86)))
             1
           0)))

;; The overflow flag is 1 iff the sum doesn't fit in the destination
(defthm add-of
  (equal (get-flag :of (add x86))
         (let ((sum (+ (logext 32 (rax x86))
                       (logext 32 (rbx x86)))))
           (if (or (< sum (- (expt 2 31))) ; sum too small
                   (<= (expt 2 31) sum) ; sum too big
                   )
               1 ; overflow
             0   ; no overflow
             )))
  :hints (("Goal" :in-theory (enable of-spec32 signed-byte-p))))


;; todo: more flags...

;; All memory addresses are unchanged
(defthm add-memory-unchanged
  (equal (memi address (add x86))
         (memi address x86)))

;; todo: more properties...
