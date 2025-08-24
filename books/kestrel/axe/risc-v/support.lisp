; Support for proofs about 32-bit RISC-V code
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

;; todo: organize this material.  some of these are theorems about the risc-v model.  others mix in our notions or normal forms

(include-book "portcullis")
(include-book "risc-v-rules") ; drop?
;(include-book "kestrel/risc-v/portcullis" :dir :system)
(include-book "kestrel/risc-v/specialized/execution32" :dir :system)
(include-book "kestrel/memory/memory32" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(include-book "kestrel/bv/bvcat2" :dir :system)

(in-theory (disable floor ash))

(acl2::defopeners STEP32N)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "kestrel/bv/bvchop" :dir :system)
(local (include-book "kestrel/bv/logapp" :dir :system)) ; reduce
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/ash" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/bv/logand" :dir :system))
(local (include-book "kestrel/bv/intro" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/bv-lists/bvchop-list" :dir :system))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system))

(local (in-theory (disable acl2::bvchop-plus-1-split))) ;todo

;todo: (ash (ash val -24) 24)

;(local (in-theory (enable ubyte32p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Open to expose read32-xreg-unsigned
(in-theory (enable read32-xreg-signed))

;; (defthm read32-xreg-signed-of-write32-pc
;;   (equal (read32-xreg-signed reg (write32-pc pc stat))
;;          (read32-xreg-signed reg stat))
;;   :hints (("Goal" :in-theory (enable write32-pc read32-xreg-unsigned))))


(local (in-theory (enable ubyte8-fix ubyte8p)))

;; better for our purposes that the non-bv rule
(defthm read32-mem-ubyte8-of-write32-mem-ubyte8-same-bv
  (equal (read32-mem-ubyte8 addr (write32-mem-ubyte8 addr val stat))
         (bvchop 8 val))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm read32-mem-ubyte8-of-write32-mem-ubyte8-irrel
  (implies (not (equal (bvchop 32 addr1) (bvchop 32 addr2)))
           (equal (read32-mem-ubyte8 addr1 (write32-mem-ubyte8 addr2 val stat))
                  (read32-mem-ubyte8 addr1 stat)))
  :hints (("Goal" :in-theory (enable read32-mem-ubyte8 write32-mem-ubyte8))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defopeners exec32-instr :hyps ((syntaxp (quotep riscv::instr))))

(local (in-theory (disable update-nth)))

(defthm write32-mem-ubyte8-of-bvchop
  (equal (write32-mem-ubyte8 (bvchop 32 addr) val state)
         (write32-mem-ubyte8 addr val state))
  :hints (("Goal" :in-theory (enable write32-mem-ubyte8))))

(in-theory (disable (:e repeat))) ; avoid out-of-memory error

(defthm read32-mem-ubyte32-of-write32-mem-ubyte32-when-disjoint-regions32p
  (implies (and (x::disjoint-regions32p 4 addr1 4 addr2)
                (integerp addr1)
                (integerp addr2))
           (equal (read32-mem-ubyte32-lendian addr1 (write32-mem-ubyte32-lendian addr2 val stat))
                  (read32-mem-ubyte32-lendian addr1 stat)))
  :hints (("Goal" :in-theory (enable read32-mem-ubyte32-lendian
                                     write32-mem-ubyte32-lendian
                                     acl2::bvchop-of-+-becomes-bvplus))))

(defthmd read32-mem-ubyte32-lendian-alt-def
  (equal (read32-mem-ubyte32-lendian addr stat)
         (b* ((b0 (read32-mem-ubyte8 addr stat))
              (b1 (read32-mem-ubyte8 (+ 1 (ifix addr))
                                     stat))
              (b2 (read32-mem-ubyte8 (+ 2 (ifix addr))
                                     stat))
              (b3 (read32-mem-ubyte8 (+ 3 (ifix addr))
                                     stat)))
           (bvcat2 8 b3 8 b2 8 b1 8 b0)))
  :hints (("Goal" :in-theory (e/d (read32-mem-ubyte32-lendian acl2::bvcat logapp ash) (acl2::logapp-equal-rewrite)))))

(defthmd ash-when-<-becomes-floor
  (implies (and (< c 0)
                (integerp i)
                (integerp c))
           (equal (ash i c)
                  (floor i (expt 2 (- c)))))
  :hints (("Goal" :in-theory (e/d (ash acl2::floor-normalize-denominator) (acl2::floor-of-*-of-/-and-1)))))

(in-theory (disable logand))

(defthmd write32-mem-ubyte32-lendian-alt-def
  (implies (integerp addr)  ;why?
           (equal (write32-mem-ubyte32-lendian addr val stat)
                  (b* (;(val (ubyte32-fix val))
                       (b0 (bvchop 8 val))
                       (b1 (slice 15 8 val))
                       (b2 (slice 23 16 val))
                       (b3 (slice 31 24 val))
                       (stat (write32-mem-ubyte8 addr b0 stat))
                       (stat (write32-mem-ubyte8 (+ 1 (ifix addr))
                                                 b1 stat))
                       (stat (write32-mem-ubyte8 (+ 2 (ifix addr))
                                                 b2 stat))
                       (stat (write32-mem-ubyte8 (+ 3 (ifix addr))
                                                 b3 stat)))
                    stat)))
  :hints (("Goal" :in-theory (enable write32-mem-ubyte32-lendian slice ubyte32-fix
                                     ;logtail
                                     acl2::bvchop-of-logtail
                                     ash-when-<-becomes-floor
                                     acl2::floor-of-power-of-2-becomes-logtail))))


(defthm read32-mem-ubyte32-of-write32-mem-ubyte32-same
  (implies (integerp addr)
           (equal (read32-mem-ubyte32-lendian addr (write32-mem-ubyte32-lendian addr val stat))
                  (bvchop 32 val)))
  :hints (("Goal" :in-theory (enable read32-mem-ubyte32-lendian-alt-def
                                     write32-mem-ubyte32-lendian-alt-def
                                     acl2::bvchop-of-+-becomes-bvplus
                                     ubyte8-fix ubyte8p ubyte32-fix ubyte32p))))

(defthmd write32-mem-ubyte8-of-+-arg1
  (implies (and (integerp addr1)
                (integerp addr2))
           (equal (write32-mem-ubyte8 (+ addr1 addr2) val stat)
                  (write32-mem-ubyte8 (bvplus 32 addr1 addr2) val stat)))
  :hints (("Goal" :in-theory (enable write32-mem-ubyte8 bvplus))))

(defthmd read32-mem-ubyte8-of-+-arg1
  (implies (and (integerp addr1)
                (integerp addr2))
           (equal (read32-mem-ubyte8 (+ addr1 addr2) stat)
                  (read32-mem-ubyte8 (bvplus 32 addr1 addr2) stat)))
  :hints (("Goal" :in-theory (enable read32-mem-ubyte8 bvplus))))

(defthmd write32-mem-ubyte32-lendian-of-+-arg1
  (implies (and (integerp addr1)
                (integerp addr2))
           (equal (write32-mem-ubyte32-lendian (+ addr1 addr2) val stat)
                  (write32-mem-ubyte32-lendian (bvplus 32 addr1 addr2) val stat)))
  :hints (("Goal" :in-theory (enable write32-mem-ubyte32-lendian write32-mem-ubyte8-of-+-arg1 acl2::bvplus-of-+-arg3))))

(defthmd read32-mem-ubyte32-lendian-of-+-arg1
  (implies (and (integerp addr1)
                (integerp addr2))
           (equal (read32-mem-ubyte32-lendian (+ addr1 addr2) stat)
                  (read32-mem-ubyte32-lendian (bvplus 32 addr1 addr2) stat)))
  :hints (("Goal" :in-theory (enable read32-mem-ubyte32-lendian read32-mem-ubyte8-of-+-arg1 acl2::bvplus-of-+-arg3))))

;; why?  tau seems to know this
(defthm integerp-of-read32-xreg-unsigned
  (integerp (read32-xreg-unsigned reg stat)))

(defthmd write32-xreg-of-+-arg2
  (implies (and (integerp v1)
                (integerp v2))
           (equal (write32-xreg reg (+ v1 v2) stat)
                  (write32-xreg reg (bvplus 32 v1 v2) stat)))
  :hints (("Goal" :in-theory (enable write32-xreg bvplus))))

(defthm write32-xreg-of-+-bvchop-arg2
  (equal (write32-xreg reg (bvchop 32 val) stat)
         (write32-xreg reg val stat))
  :hints (("Goal" :in-theory (enable write32-xreg))))

(defthm ubyte32p-of-bvchop
  (ubyte32p (bvchop '32 x))
  :hints (("Goal" :in-theory (enable ubyte32p))))

(defthm unsigned-byte-listp-of-ubyte32-list-fix
  (unsigned-byte-listp 32 (acl2::ubyte32-list-fix x))
  :hints (("Goal" :in-theory (enable acl2::ubyte32-list-fix ubyte32-fix))))

(defthm unsigned-byte-listp-of-stat32i->xregs
  (unsigned-byte-listp 32 (stat32i->xregs stat))
  :hints (("Goal" :in-theory (enable stat32i->xregs xregs32i-fix))))

(defthmd write32-xreg-when-equal-of-read32-xreg-unsigned
  (implies (equal val (read32-xreg-unsigned reg stat))
           (equal (write32-xreg reg val stat)
                  (stat32i-fix stat)))
  :hints (("Goal" :in-theory (enable write32-xreg
                                     ubyte5-fix
                                     xregs32i-fix
                                     read32-xreg-unsigned
                                     xregs32ip
                                     ;ubyte32p
                                     ))))

(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(defthm write32-xreg-of-write32-xreg-diff
  (implies (and (acl2::smaller-termp reg2 reg1)
                (not (equal reg1 reg2)))
           (equal (write32-xreg reg1 val1 (write32-xreg reg2 val2 stat))
                  (write32-xreg reg2 val2 (write32-xreg reg1 val1 stat))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable write32-xreg xregs32i-fix acl2::ubyte32-list-fix xregs32ip ubyte32p ubyte5-fix))))

;
;         (write32-xreg
 ;             2
  ;            (bvchop 32 (read32-xreg-unsigned 2 stat))


;todo: write of the read rule for mem
