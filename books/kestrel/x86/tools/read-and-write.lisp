; Simpler functions for reading and writing memory
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book introduces simpler functions for reading and writing from the x86
;; memory (read-byte, read, write-byte, and write).

(include-book "support-x86") ;for things like rb-in-terms-of-nth-and-pos-eric and canonical-address-p-between
;(include-book "projects/x86isa/machine/application-level-memory" :dir :system) ;for canonical-address-p
(include-book "flags")
(include-book "projects/x86isa/proofs/utilities/app-view/top" :dir :system) ;reduce?
(include-book "kestrel/bv/rules3" :dir :system) ;reduce?
(include-book "kestrel/bv/slice" :dir :system)
(include-book "kestrel/bv/rules10" :dir :system)
;(include-book "linear-memory")
;(include-book "support") ;reduce?
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/bv/arith" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;todo

;;
;; library additions
;;

(defthmd <-of-bvchop-when-signed-byte-p-1
  (implies (and (signed-byte-p 48 x)
                (natp x))
           (not (< (bvchop 48 x) x)))
  :hints (("Goal" :cases ((< x 0)(equal x 0))
           :in-theory (enable signed-byte-p))))

(defthmd <-of-bvchop-when-signed-byte-p-2
  (implies (and (signed-byte-p 48 x)
                (not (natp x)))
           (not (< (bvchop 48 x) x)))
  :hints (("Goal" :cases ((< x 0)(equal x 0))
           :in-theory (enable signed-byte-p))))

(defthm <-of-bvchop-when-signed-byte-p
  (implies (signed-byte-p 48 x)
           (not (< (bvchop 48 x) x)))
  :hints (("Goal" :use (<-of-bvchop-when-signed-byte-p-1
                        <-of-bvchop-when-signed-byte-p-2))))

(defthm memi-of-!memi
  (implies (unsigned-byte-p 48 addr)
           (equal (memi addr (!memi addr val x86))
                  (bvchop 8 val)))
  :hints (("Goal" :in-theory (enable memi))))

(defthm xr-app-view-of-!memi
  (equal (xr :app-view nil (!memi addr val x86))
         (xr :app-view nil x86))
  :hints (("Goal" :in-theory (enable !memi))))

(defthm app-view-of-!memi
  (equal (app-view (!memi addr val x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable !memi))))

(defthm x86p-of-!memi
  (implies (and (x86p x86)
                (INTEGERP ADDR)
                (UNSIGNED-BYTE-P 8 VAL))
           (x86p (!memi addr val x86)))
  :hints (("Goal" :in-theory (enable !memi))))

(defthm !memi-of-!memi-same
  (equal (!MEMI addr val (!MEMI addr val2 X86))
         (!MEMI addr val X86)))

;; (defthm s-of-s-both
;;   (implies (syntaxp (acl2::smaller-termp addr2 addr))
;;            (equal (sz addr val (sz addr2 val2 rec))
;;                   (if (equal addr addr2)
;;                       (sz addr val rec)
;;                     (sz addr2 val2 (sz addr val rec))))))


(defthm <-of-len-of-update-nth
  (implies (natp n)
           (< n (LEN (UPDATE-NTH n val lst))))
  :hints (("Goal" :in-theory (e/d (update-nth nfix)
                                  (;ACL2::LEN-OF-CDR-BETTER
                                   )))))

(defthm xw-of-xw-both
  (implies (and (syntaxp (acl2::smaller-termp addr2 addr))
;                (canonical-address-p addr)
 ;               (canonical-address-p addr2)
                )
           (equal (xw :mem addr val (xw :mem addr2 val2 x86))
                  (if (equal addr addr2)
                      (xw :mem addr val x86)
                    (xw :mem addr2 val2 (xw :mem addr val x86)))))
  :hints (("Goal" :in-theory (e/d (xw ;x86isa::!memi*
                                   )
                                  (;ACL2::UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-NEW
                                   ;ACL2::UPDATE-NTH-WITH-LAST-VAL-GEN
;                                   ACL2::UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                                   ;ACL2::LEN-WHEN-PSEUDO-DAGP-AUX
;ACL2::LEN-OF-CDR-BETTER
                                   )))))

(defthm xw-of-xw-diff
  (implies (and (syntaxp (acl2::smaller-termp addr2 addr))
;                (canonical-address-p addr)
 ;               (canonical-address-p addr2)
                (not (equal addr addr2))
                )
           (equal (xw :mem addr val (xw :mem addr2 val2 x86))
                  (xw :mem addr2 val2 (xw :mem addr val x86))))
  :hints (("Goal" :in-theory (e/d (xw
                                   ;;x86isa::!memi*
                                   )
                                  (;ACL2::UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-NEW
                                   ;ACL2::UPDATE-NTH-WITH-LAST-VAL-GEN
;                                   ACL2::UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                                   ;ACL2::LEN-WHEN-PSEUDO-DAGP-AUX
;ACL2::LEN-OF-CDR-BETTER
                                   )))))

(defthm <-of-bvchop-same
  (implies (integerp x)
           (equal (< (BVCHOP 48 x) x)
                  (and (natp x)
                       (not (unsigned-byte-p 48 x))))))

(defthm canonical-address-p-hack
  (implies (and (< (bvchop 48 addr2) addr2)
                (integerp addr2)
                (natp n))
           (not (canonical-address-p (+ -1 addr2 n))))
  :hints (("Goal" :in-theory (enable canonical-address-p unsigned-byte-p signed-byte-p))))

(defthm memi-of-set-flag
  (equal (memi addr (set-flag flag val x86))
         (memi addr x86))
  :hints (("Goal" :in-theory (enable memi set-flag))))

(defthm memi-of-xw-irrel
  (implies (not (equal fld :mem))
           (equal (memi addr (xw fld index val x86))
                  (memi addr x86)))
  :hints (("Goal" :in-theory (e/d (memi)
                                  (;x86isa::memi-is-n08p ;does forcing
                                   )))))

;;
;; read-byte
;;

;; Read a byte from address ADDR, which should be a canonical address.  This is
;; similar to RVM08 but without the error checks and the multiple values.
;; Negative canonical addresses get mapped to the upper half of the 2^48 byte
;; range.
;todo: define a read-bytes that calls this (and returns a list)?
;todo: enable this less below, using rules instead?
(defund read-byte (addr x86)
  (declare (xargs :stobjs x86
                  :guard (integerp addr)))
  (bvchop 8 (memi (bvchop 48 addr) X86)))

(defthm unsigned-byte-p-of-read-byte-simple
  (unsigned-byte-p 8 (read-byte addr x86))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm natp-of-read-byte
  (natp (read-byte addr x86))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm read-byte-of-xw-irrel
  (implies (not (equal fld :mem))
           (equal (read-byte base-addr (xw fld index val x86))
                  (read-byte base-addr x86)))
  :hints (("Goal" :in-theory (e/d (read-byte)
                                  (;x86isa::memi-is-n08p ;does forcing
                                   )))))

(defthm read-byte-of-set-flag
  (equal (read-byte base-addr (set-flag flag val x86))
         (read-byte base-addr x86))
  :hints (("Goal" :in-theory (e/d (read-byte)
                                  (;x86isa::memi-is-n08p ;does forcing
                                   )))))

(defthm read-byte-of-bvchop-arg1
  (equal (read-byte (bvchop 48 addr) x86)
         (read-byte addr x86))
  :hints (("Goal" :in-theory (e/d (read-byte)
                                  (;x86isa::memi-is-n08p ;does forcing
                                   )))))

(defthm read-byte-equal-when-bvchops-equal
  (implies (and (equal (bvchop 48 ad1) (bvchop 48 ad2))
                (integerp ad1)
                (integerp ad2))
           (equal (equal (read-byte ad1 x86) (read-byte ad2 x86))
                  t))
  :hints (("Goal" :use ((:instance read-byte-of-bvchop-arg1
                                   (addr ad1))
                        (:instance read-byte-of-bvchop-arg1
                                   (addr ad2)))
           :in-theory (disable read-byte-of-bvchop-arg1))))

(defthm read-byte-of-+-of-bvchop-arg1
  (implies (and (integerp x)
                (integerp y))
           (equal (read-byte (+ x (bvchop 48 y)) x86)
                  (read-byte (+ x y) x86))))

(defthm read-byte-of-+-of-bvchop-arg2
  (implies (and (integerp x)
                (integerp y))
           (equal (read-byte (+ (bvchop 48 y) x) x86)
                  (read-byte (+ y x) x86))))

(defthm read-byte-of-+-subst-constant-arg1
  (implies (and (equal (bvchop 48 x) freek)
                (syntaxp (and (quotep freek)
                              (not (quotep x))))
                (integerp x)
                (integerp y))
           (equal (read-byte (+ x y) x86)
                  (read-byte (+ freek y) x86))))

(defthm read-byte-of-+-subst-constant-arg2
  (implies (and (equal (bvchop 48 y) freek)
                (syntaxp (and (quotep freek)
                              (not (quotep y))))
                (integerp x)
                (integerp y))
           (equal (read-byte (+ x y) x86)
                  (read-byte (+ x freek) x86))))

(defthm rvm08-becomes-read-byte
  (implies (and (canonical-address-p addr)
                (x86p x86))
           (equal (mv-nth 1 (rvm08 addr x86))
                  (read-byte addr x86)))
  :hints (("Goal" :in-theory (enable read-byte rvm08 n48))))

;;
;; read
;;

;; Read an N-byte chunk starting at ADDR (in little endian fashion).
(defun read (n addr x86)
  (declare (xargs :stobjs x86
                  :guard (and (natp n)
                              (integerp addr))))
  (if (zp n)
      0
    (let ((byte (read-byte addr x86))
          (rest-bytes (read (- n 1) (+ 1 addr) x86)))
      (bvcat (* 8 (- n 1))
             rest-bytes
             8
             byte))))

(in-theory (disable ;memi$inline
            n48$inline
            ;;app-view$inline
            ))

(defthm unsigned-byte-p-of-read
  (implies (<= (* n 8) size)
           (equal (unsigned-byte-p size (read n base-addr x86))
                  (natp size)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm ash-of-read
  (implies (natp n)
           (equal (ash (read n base-addr x86)
                       8)
                  (bvcat (* 8 n)
                         (read n base-addr x86)
                         8
                         0)))
  :hints (("Goal" :use (:instance acl2::ash-becomes-bvcat
                                  (x (read n base-addr x86))
                                  (amt 8)
                                  (xsize (* 8 n)))
           :in-theory (disable acl2::ash-becomes-bvcat
                               acl2::bvcat-equal-rewrite-alt
                               acl2::bvcat-equal-rewrite)
           :do-not '(generalize eliminate-destructors))))


;; (thm
;;  (implies (unsigned-byte-p 8 x)
;;           (equal (LOGIOR x
;;                          (ASH (READ n BASE-ADDR X86)
;;                               8))
;;                  (bvcat (* 8 n)
;;                               (READ n BASE-ADDR X86)
;;                               8
;;                               x)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm mv-nth-1-of-rb-1-becomes-read
  (implies (and (app-view x86)
                (x86p x86)
                (canonical-address-p base-addr)
                (implies (posp n) (canonical-address-p (+ -1 n base-addr)))
                )
           (equal (mv-nth 1 (rb-1 n base-addr r-x x86))
                  (read n base-addr x86)))
  :hints (("Subgoal *1/2" :cases ((equal n 1))
           :expand ((RB-1 1 BASE-ADDR R-X X86))
           )
          ("Goal" :in-theory (e/d (rb-1 acl2::slice-too-high-is-0-new n48 app-view read-byte)
                                  ( ;acl2::bvcat-equal-rewrite-alt acl2::bvcat-equal-rewrite
                                   ))
           :do-not '(generalize eliminate-destructors))))

(defthm mv-nth-1-of-rb-becomes-read
  (implies (and (app-view x86)
                (x86p x86)
                (canonical-address-p base-addr)
                (implies (posp n) (canonical-address-p (+ -1 n base-addr))))
           (equal (mv-nth 1 (rb n base-addr r-x x86))
                  (read n base-addr x86)))
  :hints (("Goal" :in-theory (e/d (rb memi app-view)
                                  (acl2::bvcat-equal-rewrite-alt acl2::bvcat-equal-rewrite))
           :do-not '(generalize eliminate-destructors))))

;; Just the reverse of the above
(defthmd read-becomes-mv-nth-1-of-rb
  (implies (and (app-view x86)
                (x86p x86)
                (canonical-address-p base-addr)
                (implies (posp n) (canonical-address-p (+ -1 n base-addr))))
           (equal (read n base-addr x86)
                  (mv-nth 1 (rb n base-addr r-x x86))))
  :hints (("Goal" :by mv-nth-1-of-rb-becomes-read)))

(defthm read-of-xw-irrel
  (implies (not (equal fld :mem))
           (equal (read n base-addr (xw fld index val x86))
                  (read n base-addr x86)))
  :hints (("Goal" :in-theory (enable memi))))

(defthm read-of-set-flag
  (equal (read n base-addr (set-flag flag val x86))
         (read n base-addr x86))
  :hints (("Goal" :in-theory (enable memi))))

;todo: compare to read-when-program-at
(defthm read-in-terms-of-nth-and-pos-eric
  (implies (and ;; find that a program is loaded in the initial state:
            (program-at paddr bytes x86-init) ;these are free vars
            ;; try to prove that the same program is loaded in the current state:
            (program-at paddr bytes x86)
            (byte-listp bytes)
            (<= paddr addr)
            (integerp addr)
;           (integerp paddr)
            (< addr (+ paddr (len bytes)))
;            (member-p addr addresses)
            (canonical-address-p paddr)
            (canonical-address-p (+ -1 (len bytes) paddr))
;(canonical-address-listp addresses)
            (app-view x86)
            (app-view x86-init)
            (x86p x86) ;too bad
            )
           (equal (read 1 addr x86)
                  (nth (- addr paddr)
                       bytes)))
  :hints (("Goal" :use (:instance x86isa::rb-in-terms-of-nth-and-pos-eric
                                  (x86isa::paddr paddr)
                                  (x86isa::addr addr)
                                  (x86isa::bytes bytes)
                                  (x86isa::x86-init x86-init))
           :expand (rb-1 1 addr r-w-x x86) ;(rb-1 1 addr r-w-x x86)
           :in-theory (e/d (memi ;memi*
                                 xr rb rb-1  n48
;PROGRAM-AT
                                 app-view ;X86ISA::APP-VIEW*
                                 )
                           (read
                            x86isa::rb-in-terms-of-nth-and-pos-eric
;x86isa::rb-in-terms-of-nth-and-pos-eric-gen
                            )))))

;;
;; write-byte
;;

(defund write-byte (base-addr byte x86)
  (declare (xargs :stobjs x86
                  :guard (and (acl2::unsigned-byte-p 8 byte)
                              (integerp base-addr))))
  (!memi (bvchop 48 base-addr)
         (bvchop 8 byte)
         X86))

(defthm write-byte-of-bvchop-arg2
  (equal (write-byte ad (bvchop 8 val) x86)
         (write-byte ad val x86))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm xr-of-write-byte
  (implies (not (equal :mem fld))
           (equal (xr fld index (write-byte base-addr byte x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm x86p-of-write-byte
  (implies (x86p x86)
           (x86p (write-byte base-addr byte x86)))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm 64-bit-modep-of-write-byte
  (equal (64-bit-modep (write-byte base-addr byte x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm app-view-of-write-byte
  (equal (app-view (write-byte base-addr byte x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm alignment-checking-enabled-p-of-write-byte
  (equal (alignment-checking-enabled-p (write-byte base-addr byte x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm write-byte-of-xw-irrel
  (implies (not (equal :mem fld))
           (equal (write-byte addr byte (xw fld index val x86))
                  (xw fld index val (write-byte addr byte x86))))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm set-flag-of-write-byte
  (equal (set-flag flg val (write-byte addr byte x86))
         (write-byte addr byte (set-flag flg val x86)))
  :hints (("Goal" :in-theory (enable set-flag wb write-byte))))

(defthm get-flag-of-write-byte
  (equal (get-flag flg (write-byte addr byte x86))
         (get-flag flg x86))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm write-byte-of-bvchop-arg1
  (equal (write-byte (bvchop 48 ad) byte x86)
         (write-byte ad byte x86))
  :hints (("Goal"
           :in-theory (enable write-byte))))

(defthm read-byte-of-write-byte
  (implies (and (integerp addr2)
                (integerp addr1))
           (equal (read-byte addr1 (write-byte addr2 byte x86))
                  (if (equal (bvchop 48 addr1)
                             (bvchop 48 addr2))
                      (bvchop 8 byte)
                    (read-byte addr1 x86))))
  :hints (("Goal" :in-theory (enable read-byte write-byte ;MEMI$INLINE X86ISA::!MEMI*
                                     ))))

(defthm write-byte-of-write-byte-same
  (implies (integerp ad)
           (equal (write-byte ad byte1 (write-byte ad byte2 x86))
                  (write-byte ad byte1 x86)))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm write-byte-subst-term-arg1
  (implies (and (equal (bvchop 48 ad) (bvchop 48 free))
                (syntaxp (acl2::smaller-termp free ad))
                (integerp ad)
                (integerp free))
           (equal (write-byte ad byte x86)
                  (write-byte free byte x86)))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm write-byte-subst-arg1
  (implies (and (equal (bvchop 48 ad) freek)
                (syntaxp (and (quotep freek)
                              (not (quotep ad))))
                (integerp ad)
                (integerp freek))
           (equal (write-byte ad byte x86)
                  (write-byte freek byte x86))))


(defthm write-byte-of-write-byte-diff
  (implies (and (syntaxp (acl2::smaller-termp ad2 ad1))
                (not (equal (bvchop 48 ad1)
                            (bvchop 48 ad2)))
                (integerp ad1)
                (integerp ad2))
           (equal (write-byte ad1 byte1 (write-byte ad2 byte2 x86))
                  (write-byte ad2 byte2 (write-byte ad1 byte1 x86))))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm write-byte-of-write-byte-gen
  (implies (and (syntaxp (acl2::smaller-termp ad2 ad1))
                (integerp ad1)
                (integerp ad2))
           (equal (write-byte ad1 byte1 (write-byte ad2 byte2 x86))
                  (if (equal (bvchop 48 ad1)
                             (bvchop 48 ad2))
                      (write-byte ad1 byte1 x86)
                    (write-byte ad2 byte2 (write-byte ad1 byte1 x86)))))
  :hints (("Goal" :in-theory (enable write-byte))))

;;
;; write
;;

;; Write the N-byte chunk VAL starting at BASE-ADDR (in little endian fashion).
(defun write (n base-addr val x86)
  (declare (xargs :stobjs x86
                  :guard (and (natp n)
                              (unsigned-byte-p (* 8 n) val)
                              (integerp base-addr))))
  (if (zp n)
      x86
    (let ((x86 (write-byte base-addr (bvchop 8 val) X86)))
      (write (+ -1 n)
             (+ 1 base-addr)
             (logtail 8 val) ;(slice (+ -1 (* 8 n)) 8 val)
             x86))))

(defthm write-of-0
  (equal (write 0 ad val x86)
         x86))

(defthm mv-nth-1-of-wb-1-becomes-write
  (implies (and (app-view x86)
                (x86p x86)
                (canonical-address-p base-addr)
                (implies (posp n) (canonical-address-p (+ -1 n base-addr)))
                )
           (equal (mv-nth 1 (wb-1 n base-addr w val x86))
                  (write n base-addr val x86)))
  :hints (("Subgoal *1/3" :cases ((equal n 1)))
          ("Goal" :in-theory (e/d (wb-1 wvm08 acl2::slice-too-high-is-0-new n48 write write-byte)
                                  ( ;acl2::bvcat-equal-rewrite-alt acl2::bvcat-equal-rewrite
                                   ))
           :induct (wb-1 n base-addr w val x86)
           :expand ((write n base-addr val x86)
                    (wb-1 1 base-addr w val x86)
                    (write 1 base-addr val x86))
           :do-not '(generalize eliminate-destructors))))

(defthm mv-nth-1-of-wb-becomes-write
  (implies (and (app-view x86)
                (x86p x86)
                (canonical-address-p base-addr)
                (implies (posp n) (canonical-address-p (+ -1 n base-addr)))
                )
           (equal (mv-nth 1 (wb n base-addr w val x86))
                  (write n base-addr val x86)))
  :hints (("Goal" :in-theory (e/d (wb app-view)
                                  (wb-1 write)))))

;; TODO make a version of separate without the r-w-x stuff and that handles wrap-around??...

(defthm memi-of-bvchop-and-write
  (implies (and (or (<= (+ n2 addr2) addr1)
                    (<= (+ 1 addr1) addr2))
                (canonical-address-p addr1)
                (canonical-address-p addr2)
                (implies (posp n2) (canonical-address-p (+ -1 n2 addr2))))
           (equal (memi (bvchop 48 addr1) (write n2 addr2 val x86))
                  (memi (bvchop 48 addr1) x86)))
  :hints (("subgoal *1/2" :cases ((equal 1 n2)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (write n2 addr2 val x86)
           :in-theory (e/d (write memi separate write-byte acl2::equal-of-bvchop-and-bvchop)
                           ( ;!memi$inline
                            )))))

(defthm xr-mem-of-bvchop-and-write
  (implies (and (or (<= (+ n2 addr2) addr1)
                    (<= (+ 1 addr1) addr2))
                (canonical-address-p addr1)
                (canonical-address-p addr2)
                (implies (posp n2) (canonical-address-p (+ -1 n2 addr2))))
           (equal (xr :mem (bvchop 48 addr1) (write n2 addr2 val x86))
                  (xr :mem (bvchop 48 addr1) x86)))
  :hints (("subgoal *1/2" :cases ((equal 1 n2)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (write n2 addr2 val x86)
           :in-theory (e/d (write memi separate write-byte acl2::equal-of-bvchop-and-bvchop)
                           ( ;!memi$inline
                            )))))

(defthm xr-of-write
  (implies (not (equal :mem fld))
           (equal (xr fld index (write n base-addr val x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable write))))

(defthm x86p-of-write
  (implies (x86p x86)
           (x86p (write n base-addr val x86)))
  :hints (("Goal" :in-theory (enable write))))

(defthm 64-bit-modep-of-write
  (equal (64-bit-modep (write n addr val x86))
         (64-bit-modep x86)))

(defthm app-view-of-write
  (equal (app-view (write n addr val x86))
         (app-view x86)))

(defthm alignment-checking-enabled-p-of-write
  (equal (alignment-checking-enabled-p (write n addr val x86))
         (alignment-checking-enabled-p x86)))

(defthm write-of-xw-irrel
  (implies (not (equal :mem fld))
           (equal (write n addr value (xw fld index val x86))
                  (xw fld index val (write n addr value x86)))))

(defthm set-flag-of-write
  (equal (set-flag flg val (write n addr value x86))
         (write n addr value (set-flag flg val x86)))
  :hints (("Goal" :in-theory (enable set-flag wb write))))

;todo: add theory-invar
;todo: gen?
(defthmd write-of-set-flag
  (implies (app-view x86)
           (equal (write n addr value (set-flag flg val x86))
                  (set-flag flg val (write n addr value x86))))
  :hints (("Goal" :in-theory (enable set-flag wb write))))

(defthm get-flag-of-write
  (equal (get-flag flg (write n addr value x86))
         (get-flag flg x86))
  :hints (("Goal" :in-theory (enable set-flag wb))))




;;
;; lemmas about read and write
;;

(defthm xr-of-write-too-low
  (implies (and (< addr1 addr2)
                (natp n)
;                (x86p x86)
                (canonical-address-p addr1)
                (canonical-address-p addr2)
                (implies (posp n) (canonical-address-p (+ -1 n addr2)))
                )
           (equal (xr :mem addr1 (write n addr2 val x86))
                  (xr :mem addr1 x86)))
  :hints (("Goal" :in-theory (enable write CANONICAL-ADDRESS-P write-byte))))

;; (defthm xr-of-write-too-low-2
;;   (implies (and (< addr1 (bvchop 48 addr2))
;;                 (natp n)
;;                 (x86p x86)
;;                 (unsigned-byte-p 48 addr1)
;;  ;               (unsigned-byte-p 48 addr2)
;;                 (implies (posp n) (unsigned-byte-p 48 (+ -1 n addr2)))
;;                 )
;;            (equal (xr :mem addr1 (write n addr2 val x86))
;;                   (xr :mem addr1 x86)))
;;   :hints (("Goal" :in-theory (enable write CANONICAL-ADDRESS-P))))


;todo: improve
(defthm read-of-write-disjoint
  (implies (and (or (<= (+ n2 addr2) addr1)
                    (<= (+ n1 addr1) addr2))
                (canonical-address-p addr1)
                (implies (posp n1) (canonical-address-p (+ -1 n1 addr1)))
                (canonical-address-p addr2)
                (implies (posp n2) (canonical-address-p (+ -1 n2 addr2)))
                (natp n1)
                (natp n2)
;                (x86p x86)
                )
           (equal (read n1 addr1 (write n2 addr2 val x86))
                  (read n1 addr1 x86)))
  :hints (("subgoal *1/2" :cases ((equal n1 1))
           ;:expand (WRITE N2 ADDR2 VAL X86)
           )
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (read n1 addr1 x86)
           :in-theory (enable separate canonical-address-p app-view read-byte))))

;todo: improve
(defthm read-of-write-disjoint2
  (implies (and (separate :r n1 addr1 :r n2 addr2) ;we always turn the r-w-x params of separate into :r
                (canonical-address-p addr1)
                (implies (posp n1) (canonical-address-p (+ -1 n1 addr1)))
                (canonical-address-p addr2)
                (implies (posp n2) (canonical-address-p (+ -1 n2 addr2)))
                (natp n1)
                (natp n2)
;                (x86p x86)
                )
           (equal (read n1 addr1 (write n2 addr2 val x86))
                  (read n1 addr1 x86)))
  :hints (("Goal" :use (:instance read-of-write-disjoint)
           :in-theory (e/d (separate) (read-of-write-disjoint)))))

(defthm program-at-of-write
  (implies (and (separate :r (len bytes) prog-addr :r n addr)
                (app-view x86)
                (canonical-address-p prog-addr)
                (canonical-address-p (+ -1 (len bytes) prog-addr))
                (canonical-address-p addr)
                (implies (posp n)
                         (canonical-address-p (+ -1 n addr)))
                (natp n)
                (x86p x86)
                )
           (equal (program-at prog-addr bytes (write n addr val x86))
                  (program-at prog-addr bytes x86)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (program-at ;app-view$inline
                            )
                           (rb wb)))))





(defthmd write-of-!memi-high
  (implies (and (< (+ addr2 n -1) addr)
                (natp n)
                (natp addr2)
                (integerp addr))
           (equal (write n addr2 val2 (!memi addr val x86))
                  (!memi addr val (write n addr2 val2 x86))))
  :hints (("Subgoal *1/3" :cases ((equal n 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (WRITE N ADDR2 VAL2 X86)
           :in-theory (e/d (ACL2::BVCHOP-PLUS-1-SPLIT
                            ACL2::BVCHOP-OF-SUM-CASES
                            write-byte)
                           (ACL2::BVPLUS-RECOLLAPSE))
           :expand ((:free (addr val x86) (WRITE 1 ADDR VAL X86))
                    (:free (addr val x86) (WRITE n ADDR VAL X86))))))

(defthm read-of-write-same
  (implies (and; (app-view x86)
                (canonical-address-p addr)
                (implies (posp n) (canonical-address-p (+ -1 n addr))) ;drop?
                (natp n)
;                (x86p x86)
                )
           (equal (read n addr (write n addr val x86))
                  (bvchop (* 8 n) val)))
  :hints (;("subgoal *1/2" :cases ((equal n1 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
;           :expand (WRITE N ADDR VAL X86)
;           :induct (read n addr x86)
           :in-theory (e/d (separate canonical-address-p app-view write
                                     read-byte write-byte
                                     acl2::bvchop-of-logtail-becomes-slice)
                           (;X86ISA::!MEMI$INLINE
                            )))))

;; write-of-write:

;for proving other rules
(defthmd write-becomes-mv-nth-1-of-wb-1
  (implies (and (app-view x86)
                (x86p x86)
                (canonical-address-p base-addr)
                (implies (posp n) (canonical-address-p (+ -1 n base-addr)))
                )
           (equal (write n base-addr val x86)
                  (mv-nth 1 (wb-1 n base-addr w val x86)))))

(theory-invariant (incompatible (:rewrite write-becomes-mv-nth-1-of-wb-1)
                                (:rewrite mv-nth-1-of-wb-1-becomes-write)))

(defun double-write-induct (n base-addr val val2 x86)
  (if (zp n)
      (list n base-addr val val2 x86)
    (double-write-induct (+ -1 n) (+ 1 base-addr)
                         (logtail 8 val)
                         (logtail 8 val2)
                         x86)))

;; (defthmd !memi-of-write
;;   (implies (and (< addr addr2)
;;                 (canonical-address-p addr)
;;                 (canonical-address-p addr2)
;;                 (implies (posp n) (canonical-address-p (+ -1 n addr2)))
;;                 (natp n)
;;                 )
;;            (equal (!memi addr val (write n addr2 val2 x86))
;;                   (write n addr2 val2 (!memi addr val x86))))
;;   :hints (("Subgoal *1/3" :cases ((equal n 1)))
;;           ("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand ((:free (addr val x86) (WRITE 1 ADDR VAL X86)))
;;            )))


;add -alt to name?
(defun double-write-induct-two-addrs (n base-addr base-addr2 val x86)
  (if (zp n)
      (list n base-addr base-addr2 val x86)
    (double-write-induct-two-addrs (+ -1 n)
                                   (+ 1 base-addr)
                                   (+ 1 base-addr2)
                                   (logtail 8 val)
                                   x86)))

;; this version does the !memi last
(defun write-alt (n base-addr val x86)
  (declare (xargs :stobjs x86
                  :guard (and (natp n)
                              (unsigned-byte-p (* 8 n) val)
                              (integerp base-addr))))
  (if (zp n)
      x86
      (let ((x86 (write-alt (+ -1 n)
                            (+ 1 base-addr)
                            (logtail 8 val)
                            x86)))
           (!memi (bvchop 48 base-addr)
                  (bvchop 8 val)
                  x86))))

(defthmd write-alt-when-bvchops-agree
  (implies (and (equal (bvchop 48 addr)
                       (bvchop 48 addr2))
                (integerp addr)
                (integerp addr2))
           (equal (write-alt n addr2 val x86)
                  (write-alt n addr val x86)))
  :hints (("Goal" :expand ()
           :induct (double-write-induct-two-addrs N ADDR addr2 VAL X86)
           :in-theory (e/d (ACL2::BVCHOP-OF-SUM-CASES)
                           (ACL2::BVPLUS-RECOLLAPSE)))))

(defthm write-alt-of-bvchop-48
  (implies (integerp base-addr)
           (equal (write-alt n (bvchop 48 base-addr) val x86)
                  (write-alt n base-addr val x86)))
  :hints (("Goal" :use (:instance write-alt-when-bvchops-agree
                                  (addr2 (bvchop 48 base-addr))
                                  (addr base-addr)))))

(defthm write-alt-of-plus-1-subst-constant
  (implies (and (syntaxp (not (quotep addr)))
                (equal k (bvchop 48 addr))
                (syntaxp (quotep k))
                (integerp addr))
           (equal (write-alt n (+ 1 addr) val x86)
                  (write-alt n (bvplus 48 1 k) val x86)))
  :hints (("Goal" :in-theory (e/d (bvplus) (acl2::bvplus-recollapse))
           :use (:instance write-alt-when-bvchops-agree
                           (addr (+ 1 addr))
                           (addr2 (bvplus 48 1 k))))))

(defthmd write-alt-of-!memi-irrel
  (implies (and (< n (bvchop 48 (- addr addr2))) ;no wrap around
                (integerp addr)
                (integerp addr2)
                (natp n))
           (equal (write-alt n addr2 val2 (!memi addr val x86))
                  (!memi addr val (write-alt n addr2 val2 x86))))
  :hints ( ;("Subgoal *1/3" :cases ((equal n 1)))
          ("subgoal *1/2"
           :use (:instance xw-of-xw-diff
                           (val2 (BVCHOP 8 VAL2))
                           (addr2 (bvchop 48 addr2))
                           (X86 (WRITE-ALT (+ -1 N)
                                           (+ 1 ADDR2)
                                           (LOGTAIL 8 VAL2)
                                           X86))))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (WRITE-alt N ADDR2 VAL2 X86)
           :in-theory (e/d (ACL2::BVCHOP-PLUS-1-SPLIT
                            ACL2::BVCHOP-OF-SUM-CASES)
                           (ACL2::BVPLUS-RECOLLAPSE
                            XW-OF-XW-BOTH
                            xw-of-xw-diff
                            X86ISA::XW-XW-INTRA-FIELD-ARRANGE-WRITES))
           :expand ((:free (addr val x86) (WRITE 1 ADDR VAL X86))
                    (:free (addr val x86) (WRITE n ADDR VAL X86))))))

(defthmd write-alt-of-xw-memi-irrel
  (implies (and (< n (bvchop 48 (- addr addr2))) ;no wrap around
                (integerp addr)
                (integerp addr2)
                (natp n))
           (equal (write-alt n addr2 val2 (xw :mem addr val x86))
                  (xw :mem addr val (write-alt n addr2 val2 x86))))
  :hints ( ;("Subgoal *1/3" :cases ((equal n 1)))
          ("subgoal *1/2"
           :use (:instance xw-of-xw-diff
                           (val2 (BVCHOP 8 VAL2))
                           (addr2 (bvchop 48 addr2))
                           (X86 (WRITE-ALT (+ -1 N)
                                           (+ 1 ADDR2)
                                           (LOGTAIL 8 VAL2)
                                           X86))))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (WRITE-alt N ADDR2 VAL2 X86)
           :in-theory (e/d (ACL2::BVCHOP-PLUS-1-SPLIT
                            ACL2::BVCHOP-OF-SUM-CASES)
                           (ACL2::BVPLUS-RECOLLAPSE
                            XW-OF-XW-BOTH
                            xw-of-xw-diff
                            X86ISA::XW-XW-INTRA-FIELD-ARRANGE-WRITES))
           :expand ((:free (addr val x86) (WRITE 1 ADDR VAL X86))
                    (:free (addr val x86) (WRITE n ADDR VAL X86))))))

(defthmd write-becomes-write-alt
  (implies (and (integerp addr)
                (unsigned-byte-p 48 n)
                )
           (equal (write n addr val x86)
                  (write-alt n addr val x86)))
  :hints (("Goal" :induct (write n addr val x86)
           :in-theory (e/d (write-alt-of-xw-memi-irrel ;write-alt-of-!memi-irrel
                            ACL2::BVPLUS-OF-PLUS-ARG3
                            write-byte)
                           (;X86ISA::!MEMI$INLINE
                            ))
           :expand ((WRITE N ADDR VAL X86)))))

;; (thm
;;  (implies (equal (bvchop 48 addr)
;;                  (bvchop 48 addr2))
;;           (equal (write n addr2 val x86)
;;                  (write n addr val x86)))
;;  :hints (("Goal" :expand ((WRITE N (BVCHOP 48 ADDR) VAL X86)
;;                           (WRITE N ADDR VAL X86)
;;                           (WRITE N ADDR2 VAL X86))
;;           :induct (double-write-induct-two-addrs N ADDR addr2 VAL X86)
;;           :in-theory (disable (:d write))
;;           )))

(defthmd write-of-!memi
  (implies (and (< n (bvchop 48 (- addr addr2))) ;no wrap around ;(< (bvchop 48 addr) (bvchop 48 addr2))
                (integerp addr2)
                (integerp addr))
           (equal (write n addr2 val2 (!memi addr val x86))
                  (!memi addr val (write n addr2 val2 x86))))
  :hints (("Subgoal *1/3" :cases ((equal n 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (WRITE N ADDR2 VAL2 X86)
           :in-theory (e/d (ACL2::BVCHOP-PLUS-1-SPLIT
                            ACL2::BVCHOP-OF-SUM-CASES
                            write-byte)
                           (ACL2::BVPLUS-RECOLLAPSE))
           :expand ((:free (addr val x86) (WRITE 1 ADDR VAL X86))
                    (:free (addr val x86) (WRITE n ADDR VAL X86))))))

(defthmd write-of-xw-mem
  (implies (and (< n (bvchop 48 (- addr addr2))) ;no wrap around ;(< (bvchop 48 addr) (bvchop 48 addr2))
                (integerp addr2)
                (integerp addr))
           (equal (write n addr2 val2 (xw :mem addr val x86))
                  (xw :mem addr val (write n addr2 val2 x86))))
  :hints (("Subgoal *1/3" :cases ((equal n 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (WRITE N ADDR2 VAL2 X86)
           :in-theory (e/d (ACL2::BVCHOP-PLUS-1-SPLIT
                            ACL2::BVCHOP-OF-SUM-CASES
                            write-byte)
                           (ACL2::BVPLUS-RECOLLAPSE))
           :expand ((:free (addr val x86) (WRITE 1 ADDR VAL X86))
                    (:free (addr val x86) (WRITE n ADDR VAL X86))))))

;; (defthm write-alt-of-write-alt-same
;;   (implies (and (app-view x86)
;; ;                (canonical-address-p addr)
;;  ;               (implies (posp n) (canonical-address-p (+ -1 n addr)))
;;                 (unsigned-byte-p 48 n)
;;                 (x86p x86))
;;            (equal (write-alt n addr val1 (write-alt n addr val2 x86))
;;                   (write-alt n addr val1 x86)))
;;   ;; :hints (("Goal" :in-theory (e/d (write-becomes-mv-nth-1-of-wb-1 app-view wb-1)
;;   ;;                                 (MV-NTH-1-OF-WB-1-BECOMES-WRITE write)))))
;;   :hints ( ;("subgoal *1/2" :cases ((equal n1 1)))
;;           ("Goal" :do-not '(generalize eliminate-destructors)
;; ;           :expand (WRITE N ADDR VAL X86)
;;            :induct (double-write-induct n addr val1 val2 x86)
;;            :expand ((:free (addr val x86) (WRITE 1 ADDR VAL X86))
;;                     (:free (addr val x86) (WRITE n ADDR Val X86))
;; ;                    (WRITE N ADDR VAL2 X86)
;;                     )
;;            :in-theory (e/d (separate canonical-address-p app-view
;;                                      (:i write)
;;                                      write
;;                                       WRITE-OF-!MEMI
;;                                       WRITE-ALT-OF-!MEMI-IRREL
;;                                      )
;;                            (X86ISA::!MEMI$INLINE
;;                             )))))

;gen the n's?
(defthm write-of-write-same
  (implies (and ;(app-view x86)
                (integerp addr)
                (unsigned-byte-p 48 n)
                ;(x86p x86)
                )
           (equal (write n addr val1 (write n addr val2 x86))
                  (write n addr val1 x86)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (double-write-induct n addr val1 val2 x86)
           :expand ((:free (addr val x86) (WRITE 1 ADDR VAL X86))
                    (:free (addr val x86) (WRITE n ADDR Val X86)))
           :in-theory (e/d (separate canonical-address-p app-view
                                     (:i write)
                                     write
                                     write-of-xw-mem ;WRITE-OF-!MEMI
                                     ACL2::BVPLUS-OF-PLUS-ARG3
                                     write-byte
                                     )
                           (;X86ISA::!MEMI$INLINE
                            )))))

(defthmd memi-becomes-read-1
  (implies (x86p x86)
           (equal (memi (bvchop 48 addr) x86)
                  (read 1 addr x86)))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthmd memi-becomes-read-2
  (implies (and (x86p x86)
                (integerp addr)
                (integerp n))
           (equal (memi (bvplus 48 n addr) x86)
                  (read 1 (+ n addr) x86)))
  :hints (("Goal" :in-theory (enable bvplus read-byte))))

;todo: gen
;; this is a 4-byte version of READ-IN-TERMS-OF-NTH-AND-POS-ERIC
(DEFTHM READ-IN-TERMS-OF-NTH-AND-POS-ERIC-4-bytes
  (IMPLIES (AND (PROGRAM-AT PADDR BYTES X86-INIT)
                (PROGRAM-AT PADDR BYTES X86)
                (BYTE-LISTP BYTES)
                (<= PADDR ADDR)
                (INTEGERP ADDR)
                (< (+ 3 ADDR) (+ PADDR (LEN BYTES)))
                (CANONICAL-ADDRESS-P PADDR)
                (CANONICAL-ADDRESS-P (+ -1 (LEN BYTES) PADDR))
                (APP-VIEW X86)
                (APP-VIEW X86-INIT)
                (X86P X86))
           (EQUAL (READ 4 ADDR X86)
                  (BVCAT 8 (NTH (+ 3 ADDR (- PADDR)) BYTES)
                         24
                         (BVCAT 8 (NTH (+ 2 ADDR (- PADDR)) BYTES)
                                16
                                (BVCAT 8 (NTH (+ 1 ADDR (- PADDR)) BYTES)
                                       8 (NTH (+ ADDR (- PADDR)) BYTES))))
                  ))
  :hints (("Goal" :expand ((READ 4 ADDR X86)
                           (READ 3 (+ 1 ADDR) X86)
                           (READ 2 (+ 2 ADDR) X86))
           :in-theory (e/d (memi-becomes-read-1
                            memi-becomes-read-2
                            ACL2::BVPLUS-RECOLLAPSE
                            read-byte)
                           ( ACL2::BVCAT-EQUAL-REWRITE-ALT
                             ACL2::BVCAT-EQUAL-REWRITE
                             read
                             len)))))

(defthmd read-byte-when-bvchops-agree
  (implies (and (integerp addr)
                (integerp addr2)
                (equal (bvchop 48 addr)
                       (bvchop 48 addr2)))
           (equal (equal (read-byte addr x86)
                         (read-byte addr2 x86))
                  t))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthmd read-when-bvchops-agree
  (implies (and (integerp addr)
                (integerp addr2)
                (equal (bvchop 48 addr)
                       (bvchop 48 addr2)))
           (equal (equal (read n addr x86)
                         (read n addr2 x86))
                  t))
  :hints (("Goal" :induct (double-write-induct-two-addrs N ADDR addr2 VAL X86)
           :in-theory (e/d (read
                            acl2::bvchop-of-sum-cases
                            read-byte-when-bvchops-agree
                            bvplus)
                           (ACL2::BVPLUS-RECOLLAPSE)))))

(defthm read-of-bvchop-48
  (implies (integerp addr)
           (equal (read n (bvchop 48 addr) x86)
                  (read n addr x86)))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree))))

(defun read-induct (low n addr)
  (if (zp n)
      (list low n addr)
    (read-induct (+ -1 low) (+ -1 n) (+ 1 addr))))

(defthm slice-of-read-one-byte
  (implies (and (natp low)
                (natp n)
                (< low n))
           (equal (acl2::slice (+ 7 (* 8 low)) (* 8 low) (read n addr x86))
                  (read 1 (+ low addr) x86)))
  :hints (("Goal" :induct (read-induct low n addr)
           :in-theory (enable read-byte))))

(defthm read-when-equal-of-read
  (implies (and (equal (read n2 addr2 x86) freeval)
                (syntaxp (quotep freeval))
                (posp n2)
                (<= addr2 addr)
                (< (+ addr (- addr2)) n2)
                (integerp addr)
                (integerp addr2))
           ;;todo: gen the 1:
           (equal (read 1 addr x86)
                  (acl2::slice (+ 7 (* 8 (- addr addr2))) (* 8 (- addr addr2)) freeval)))
  :hints (("Goal" :in-theory (disable read
                                      distributivity
                                      ))))

(defthmd read-when-equal-of-read-gen
  (implies (and (equal (read n2 addr2 x86) freeval)
                ;;(syntaxp (quotep freeval))
                (posp n2)
                (<= addr2 addr)
                (< (+ addr (- addr2)) n2)
                (integerp addr)
                (integerp addr2))
           ;;todo: gen the 1:
           (equal (read 1 addr x86)
                  (acl2::slice (+ 7 (* 8 (- addr addr2))) (* 8 (- addr addr2)) freeval)))
  :hints (("Goal" :in-theory (disable read
                                      distributivity
                                      ))))

(defthm read-when-equal-of-read-alt
  (implies (and (equal freeval (read n2 addr2 x86))
                (syntaxp (quotep freeval))
                (posp n2)
                (<= addr2 addr)
                (< (+ addr (- addr2)) n2)
                (integerp addr)
                (integerp addr2))
           ;;todo: gen the 1:
           (equal (read 1 addr x86)
                  (acl2::slice (+ 7 (* 8 (- addr addr2))) (* 8 (- addr addr2)) freeval)))
  :hints (("Goal" :by read-when-equal-of-read)))

(defun-nx double-write-induct-two-addrs2 (n base-addr base-addr2 val x86)
  (if (zp n)
      (list n base-addr base-addr2 val x86)
    (double-write-induct-two-addrs2 (+ -1 n)
                                    (+ 1 base-addr)
                                    (+ 1 base-addr2)
                                    (logtail 8 val)
                                    (XW :MEM (BVCHOP 48 base-ADDR)
                                        (BVCHOP 8 VAL)
                                        X86))))

(defthmd write-when-bvchops-agree
  (implies (and (equal (bvchop 48 addr)
                       (bvchop 48 addr2))
                (integerp addr)
                (integerp addr2))
           (equal (equal (write n addr2 val x86)
                         (write n addr val x86))
                  t))
  :hints (("Goal" :expand ((WRITE N ADDR2 VAL X86)
                           (WRITE N ADDR VAL X86))
           :induct (double-write-induct-two-addrs2 N ADDR addr2 VAL X86)
           :in-theory (e/d (write write-byte
                            ACL2::BVCHOP-OF-SUM-CASES)
                           (ACL2::BVPLUS-RECOLLAPSE)))))

(defthm write-of-bvchop-48
  (implies (integerp addr)
           (equal (write n (bvchop 48 addr) val x86)
                  (write n addr val x86)))
  :hints (("Goal" :use (:instance write-when-bvchops-agree
                                  (addr2 (bvchop 48 addr))
                                  (addr addr)))))

(defthm read-of-bvchop-tighten
  (implies (and (syntaxp (quotep size))
                (< 48 size)
                (integerp size))
           (equal (read n (bvchop size addr) x86)
                  (read n (bvchop 48 addr) x86)))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree))))

(defthm write-of-bvchop-tighten
  (implies (and (syntaxp (quotep size))
                (< 48 size)
                (integerp size))
           (equal (write n (bvchop size addr) val x86)
                  (write n (bvchop 48 addr) val x86)))
  :hints (("Goal" :in-theory (enable write-when-bvchops-agree))))

(defthm read-of-bvplus-tighten
  (implies (and (syntaxp (quotep size))
                (< 48 size)
                (integerp size))
           (equal (read n (bvplus size x y) x86)
                  (read n (bvplus 48 x y) x86)))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree))))

(defthm write-of-bvplus-tighten
  (implies (and (syntaxp (quotep size))
                (< 48 size)
                (integerp size))
           (equal (write n (bvplus size x y) val x86)
                  (write n (bvplus 48 x y) val x86)))
  :hints (("Goal" :in-theory (enable write-when-bvchops-agree))))

;; we use logext so that negative constants are nice
(defthm read-of-bvplus-normalize
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (integerp addr))
           (equal (read n (bvplus 48 k addr) x86)
                  (read n (+ (logext 48 k) addr) x86)))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree
                                     acl2::bvplus-recollapse))))

;; we use logext so that negative constants are nice
(defthm write-of-bvplus-normalize
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (integerp addr))
           (equal (write n (bvplus 48 k addr) val x86)
                  (write n (+ (logext 48 k) addr) val x86)))
  :hints (("Goal" :in-theory (enable write-when-bvchops-agree
                                     acl2::bvplus-recollapse))))

;todo: gen the 1
(defthm read-when-program-at
  (implies (and (program-at addr2 bytes x86)
                (syntaxp (quotep bytes))
                (< 0 (len bytes))
                (BYTE-LISTP BYTES)
                (canonical-address-p$inline addr2)
                (canonical-address-p$inline (+ -1 addr2 (len bytes)))
                (<= addr2 addr)
                (< (+ addr (- addr2)) (len bytes))
                (integerp addr)
                (integerp addr2)
                (app-view x86)
                (x86p x86))
           ;;todo: gen the 1:
           (equal (read 1 addr x86)
                  (nth (- addr addr2) bytes)))
  :hints (("Goal" :in-theory (e/d (program-at
;rb
                                   x::read-when-equal-of-read-gen
                                   )
                                  (read
                                   distributivity
                                   )))))

(defthmd read-byte-becomes-read
  (equal (read-byte addr x86)
         (read 1 addr x86))
  :hints (("Goal" :in-theory (enable read))))

(defthm read-byte-when-program-at
  (implies (and (program-at addr2 bytes x86)
                (syntaxp (quotep bytes))
                (< 0 (len bytes))
                (byte-listp bytes)
                (canonical-address-p$inline addr2)
                (canonical-address-p$inline (+ -1 addr2 (len bytes)))
                (<= addr2 addr)
                (< (+ addr (- addr2)) (len bytes))
                (integerp addr)
                (integerp addr2)
                (app-view x86)
                (x86p x86))
           (equal (read-byte addr x86)
                  (nth (- addr addr2) bytes)))
  :hints (("Goal" :use (:instance read-when-program-at)
           :in-theory (e/d (read) (read-when-program-at
                                   read-in-terms-of-nth-and-pos-eric)))))

(defthm bvplus-of-bvplus-tighten ;todo: gen?
  (equal (bvplus '48 (bvplus '64 x y) z)
         (bvplus '48 (bvplus '48 x y) z))
  :hints (("Goal" :in-theory (e/d (bvplus) (acl2::bvplus-recollapse)))))

(defthm read-of-bvplus
  (implies (and (integerp x)
                (integerp y))
           (equal (read n (bvplus 48 x y) x86)
                  (read n (+ x y) x86)))
 :hints (("Goal" :in-theory (enable read-when-bvchops-agree
                                     acl2::bvplus-recollapse))))

(defthm write-of-bvplus
  (implies (and (integerp x)
                (integerp y))
           (equal (write n (bvplus 48 x y) val x86)
                  (write n (+ x y) val x86)))
  :hints (("Goal" :in-theory (enable write-when-bvchops-agree
                                     acl2::bvplus-recollapse))))

(defthm read-of-+-normalize
  (implies (and (syntaxp (quotep k))
                (not (signed-byte-p 48 k))
                (integerp k)
                (integerp x))
           (equal (read n (+ k x) x86)
                  (read n (+ (logext 48 k) x) x86)))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree
                                     acl2::bvplus-recollapse))))

(defthm write-of-+-normalize
  (implies (and (syntaxp (quotep k))
                (not (signed-byte-p 48 k))
                (integerp k)
                (integerp x))
           (equal (write n (+ k x) val x86)
                  (write n (+ (logext 48 k) x) val x86)))
  :hints (("Goal" :in-theory (enable write-when-bvchops-agree
                                     acl2::bvplus-recollapse))))

(defthm read-of-+-of-bvplus
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (read n (+ x (bvplus 48 y z)) x86)
                  (read n (+ x y z) x86)))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree
                                     acl2::bvplus-recollapse))))

(defthm read-of-+-of-bvplus-alt
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (read n (+ (bvplus 48 y z) x) x86)
                  (read n (+ y z x) x86)))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree
                                     acl2::bvplus-recollapse))))

(defthm integerp-of-read
  (integerp (read n base-addr x86)))

(defthm <-of-read-and-non-positive
  (implies (and (syntaxp (quotep k))
                (<= k 0))
           (equal (< (read n adr x86) k)
                  nil)))

(defthm write-of-bvchop-arg3
  (implies (natp n)
           (equal (write n ad (bvchop (* 8 n) val) x86)
                  (write n ad val x86)))
  :hints (("Goal"
           :induct (write n ad val x86)
           :in-theory (e/d (acl2::logtail-of-bvchop-becomes-slice
                            acl2::bvchop-of-logtail-becomes-slice
                            write)
                           ())
           :expand ((write n ad val x86)
                    (write n ad (bvchop (* 8 n) val) x86)))))

(in-theory (disable acl2::natp-when-gte-0)) ;seems bad

(defthm write-of-bvchop-arg3-gen
  (implies (and (<= (* 8 n) m)
                (natp n)
                (natp m))
           (equal (write n ad (bvchop m val) x86)
                  (write n ad val x86)))
  :hints (("Goal" :use ((:instance write-of-bvchop-arg3 (val val))
                        (:instance write-of-bvchop-arg3 (val (bvchop m val))))
           :in-theory (disable write-of-bvchop-arg3))))

(defthm unsigned-byte-p-of-read-byte
  (implies (and (integerp n)
                (<= 8 n))
           (unsigned-byte-p n (read-byte addr x86)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-read-byte-simple)
           :in-theory (disable unsigned-byte-p-of-read-byte-simple))))

(defthm read-byte-of-logext-48
  (equal (read-byte (logext 48 addr) x86)
         (read-byte addr x86))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthmd equal-of-read-and-read-helper
  (implies (and (equal (bvchop 48 addr1) (bvchop 48 addr2))
                (integerp addr1)
                (integerp addr2))
           (equal (equal (read n addr1 x86)
                         (read n addr2 x86))
                  t))
  :hints (("Goal" :in-theory (enable))))

(defthm read-of-logext-48
  (implies (integerp addr)
           (equal (read n (logext 48 addr) x86)
                  (read n addr x86)))
  :hints (("Goal" :in-theory (e/d (equal-of-read-and-read-helper) (read)))))

;todo handle reading 4 bytes when they are written individually

(defthmd read-4-blast
  (implies (integerp addr)
           (equal (read 4 addr x86)
                  (bvcat 8
                         (read 1 (bvplus 48 3 addr) x86)
                         24
                         (bvcat 8
                                (read 1 (bvplus 48 2 addr) x86)
                                16
                                (bvcat 8
                                       (read 1 (bvplus 48 1 addr) x86)
                                       8
                                       (read 1 addr x86))))))
  :hints (("Goal" :expand ((READ 4 ADDR X86)
                           (READ 3 (+ 1 ADDR) X86)
                           (READ 2 (+ 2 ADDR) X86))
           :in-theory (e/d (read bvplus)
                           (ACL2::BVPLUS-RECOLLAPSE)))))

(defthm read-of-write-both-size-1
  (implies (and (app-view x86) ;drop
                (canonical-address-p addr)
                (canonical-address-p addr2)
                (x86p x86))
           (equal (read 1 addr (write 1 addr2 val x86))
                  (if (equal addr addr2)
                      (bvchop 8 val)
                    (read 1 addr x86))))
  :hints (("Goal" :cases ((< addr addr2)
                          (< addr2 addr))
           :in-theory (e/d (read) (write-of-0)))))

;;;
;;; write-bytes
;;;

(defun write-bytes (base-addr bytes x86)
  (declare (xargs :stobjs x86
                  :guard (and (acl2::all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (integerp base-addr))))
  (if (endp bytes)
      x86
    (let ((x86 (write-byte base-addr (first bytes) X86)))
      (write-bytes (+ 1 base-addr)
                  (rest bytes)
                  x86))))

(defthm write-bytes-of-nil
  (equal (write-bytes base-addr nil x86)
         x86))

(defthm xr-of-write-bytes
  (implies (not (equal :mem fld))
           (equal (xr fld index (write-bytes base-addr vals x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable write-bytes))))

(defthm x86p-of-write-bytes
  (implies (x86p x86)
           (x86p (write-bytes base-addr vals x86)))
  :hints (("Goal" :in-theory (enable write-bytes))))

(defthm 64-bit-modep-of-write-bytes
  (equal (64-bit-modep (write-bytes base-addr vals x86))
         (64-bit-modep x86)))

(defthm app-view-of-write-bytes
  (equal (app-view (write-bytes base-addr vals x86))
         (app-view x86)))

(defthm alignment-checking-enabled-p-of-write-bytes
  (equal (alignment-checking-enabled-p (write-bytes base-addr vals x86))
         (alignment-checking-enabled-p x86)))

(defthm write-bytes-of-xw-irrel
  (implies (not (equal :mem fld))
           (equal (write-bytes addr values (xw fld index val x86))
                  (xw fld index val (write-bytes addr values x86)))))

(defthm set-flag-of-write-bytes
  (equal (set-flag flg val (write-bytes addr values x86))
         (write-bytes addr values (set-flag flg val x86)))
  :hints (("Goal" :in-theory (enable set-flag wb write-bytes))))

(defthm get-flag-of-write-bytes
  (equal (get-flag flg (write-bytes addr values x86))
         (get-flag flg x86))
  :hints (("Goal" :in-theory (enable set-flag wb))))

;todo turn only writes of >1 byte into write-bytes..
(defthm write-bytes-when-length-is-1
  (implies (equal 1 (len bytes))
           (equal (write-bytes addr bytes x86)
                  (write-byte addr (first bytes) x86)))
  :hints (("Goal" :in-theory (e/d () ()))))
