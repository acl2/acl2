; Proofs about a 1-instruction binary that ANDs AX into a memory word (16-bit reg-to-mem)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of and_mem16_ax.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "and_mem16_ax.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Bridge: connect ax to bvchop-of-rax so Axe proofs reduce to the rax form.
(local (defthm ax-rewrite
  (equal (ax x86) (bvchop 16 (rax x86)))
  :hints (("Goal" :in-theory (enable ax rax)))))

;; Lifts the subroutine into logic: Creates the function and_mem16_ax, which
;; represents the effect of the program on the x86 state.
;; AND [RBX], AX is encoded as 66 21 03 (3 bytes), so stop PC = 0x401003.
;; Both the base address and +1 must be canonical for the 16-bit write.
(def-unrolled and_mem16_ax
  :executable "and_mem16_ax.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 1 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The word at memory address [RBX] is updated to the 16-bit AND of the original
;; word at [RBX] and AX (Intel SDM Vol 2A: AND entry: DEST <- DEST AND SRC, size = word).
(defthm and_mem16_ax-memory-at-rbx
  (equal (read 2 (rbx x86) (and_mem16_ax x86))
         (bvand 16 (read 2 (rbx x86) x86) (ax x86))))

;; All other memory bytes are unchanged (only the 2 bytes at [RBX] and [RBX+1] are written).
;; Condition: address is not within the 2-byte region starting at [RBX].
(defthm and_mem16_ax-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 2))
           (equal (read 1 address (and_mem16_ax x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (AND [RBX], AX is 3 bytes: 66 21 03)
(defthm and_mem16_ax-rip
  (equal (rip (and_mem16_ax x86))
         (+ 3 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm and_mem16_ax-registers
  (equal (rgfi reg (and_mem16_ax x86))
         (rgfi reg x86)))

;; Intel SDM Vol 2A AND entry: CF is cleared to 0.
(defthm and_mem16_ax-cf
  (equal (get-flag :cf (and_mem16_ax x86))
         0))

;; Intel SDM Vol 2A AND entry: OF is cleared to 0.
(defthm and_mem16_ax-of
  (equal (get-flag :of (and_mem16_ax x86))
         0))

;; The zero flag is 1 iff the 16-bit AND result is 0.
(defthm and_mem16_ax-zf
  (equal (get-flag :zf (and_mem16_ax x86))
         (if (equal 0 (bvand 16 (read 2 (rbx x86) x86) (ax x86)))
             1
           0))
  :hints (("Goal" :in-theory (enable zf-spec))))

;; The sign flag is the sign bit (bit 15) of the 16-bit result.
(defthm and_mem16_ax-sf
  (equal (get-flag :sf (and_mem16_ax x86))
         (getbit 15 (bvand 16 (read 2 (rbx x86) x86) (ax x86))))
  :hints (("Goal" :in-theory (disable read-2-blast))))

(local (defthm pf-spec16-alt-def
  (equal (pf-spec16 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm and_mem16_ax-pf
  (equal (get-flag :pf (and_mem16_ax x86))
         (if (evenp (bvcount 8 (bvand 16 (read 2 (rbx x86) x86) (ax x86))))
             1
           0))
  :hints (("Goal" :in-theory (e/d (pf-spec16-alt-def) (read-2-blast)))))

(defthm and_mem16_ax-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (and_mem16_ax x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
