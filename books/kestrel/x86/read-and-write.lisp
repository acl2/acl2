; Simpler functions for reading and writing memory
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book introduces simpler functions for reading and writing from the x86
;; memory (read-byte, read, write-byte, and write).

(include-book "portcullis") ; for the package
(include-book "projects/x86isa/machine/state" :dir :system) ; for memi
(include-book "canonical")
(include-book "state") ; for X86ISA::INTEGERP-OF-MEMI
(include-book "projects/x86isa/machine/linear-memory" :dir :system) ; for program-at
(include-book "support-x86") ;for things like rb-in-terms-of-nth-and-pos-eric and canonical-address-p-between
;(include-book "projects/x86isa/machine/application-level-memory" :dir :system) ;for canonical-address-p
;(include-book "projects/x86isa/proofs/utilities/app-view/top" :dir :system) ;reduce?
(include-book "kestrel/bv/rules3" :dir :system) ;reduce?
(include-book "kestrel/bv/slice" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(include-book "kestrel/bv/rules10" :dir :system)
(include-book "kestrel/bv-lists/unpackbv" :dir :system)
(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "kestrel/lists-light/finalcdr" :dir :system)
(include-book "kestrel/bv/putbits" :dir :system)
;(include-book "linear-memory")
;(include-book "support") ;reduce?
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/bv/intro" :dir :system))
(local (include-book "kestrel/bv/logior-b" :dir :system))
(local (include-book "kestrel/bv/ash" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;todo

(local (in-theory (disable ;(:linear x86isa::n08p-xr-mem)
                           acl2::unsigned-byte-p-from-bounds))) ; for speed

;;
;; library additions
;;

(local (in-theory (disable memi !memi)))

(in-theory (disable ;memi$inline
            ;n48$inline ; todo
            ;;app-view$inline
             ))

;gen
(defthm bvplus-of-bvuminus-cancel-helper
  (implies (and (integerp addr1)
                (integerp addr2))
           (equal (bvplus 48 (+ 1 addr1) (bvuminus 48 (+ 1 addr2)))
                  (bvplus 48 addr1 (bvuminus 48 addr2))))
  :hints (("Goal" :in-theory (enable bvplus bvuminus))))

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

(defthm <-of-bvchop-same
  (implies (integerp x)
           (equal (< (bvchop 48 x) x)
                  (and (<= 0 x)
                       (not (unsigned-byte-p 48 x))))))

(defthm bvplus-of-bvplus-tighten ;todo: gen?
  (equal (bvplus 48 (bvplus 64 x y) z)
         (bvplus 48 (bvplus 48 x y) z))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-combine-constants-hack
  (implies (and (integerp x)
                (integerp y))
           (equal (bvplus 48 (+ 1 x) (+ -1 y))
                  (bvplus 48 x y)))
  :hints (("Goal" :in-theory (enable bvplus))))

(theory-invariant (incompatible (:rewrite acl2::bvminus-of-+-arg3) (:rewrite acl2::bvchop-of-sum-cases)))

(in-theory (disable acl2::natp-when-gte-0)) ;questionable rule; the x86 model should not bring in std/basic/arith-equivs.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Less primitive library additions:


;; (defthm s-of-s-both
;;   (implies (syntaxp (acl2::smaller-termp addr2 addr))
;;            (equal (sz addr val (sz addr2 val2 rec))
;;                   (if (equal addr addr2)
;;                       (sz addr val rec)
;;                     (sz addr2 val2 (sz addr val rec))))))


(defthm canonical-address-p-hack
  (implies (and (< (bvchop 48 addr2) addr2)
                (integerp addr2)
                (natp n))
           (not (canonical-address-p (+ -1 addr2 n))))
  :hints (("Goal" :in-theory (enable canonical-address-p unsigned-byte-p signed-byte-p))))

;move
;; usually we get rid of rvm08 anyway.
(defthm unsigned-byte-p-of-mv-nth-1-of-rvm08
  (implies (<= 8 size)
           (equal (unsigned-byte-p size (mv-nth 1 (rvm08 x86isa::addr x86)))
                  (natp size)))
  :hints (("Goal" :use (:instance x86isa::n08p-mv-nth-1-rvm08)
           :in-theory (disable x86isa::n08p-mv-nth-1-rvm08))))

;; End of Library stuff

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reads a byte from address ADDR, which should be a canonical address.  This is
;; similar to RVM08 but without the error checks and the multiple values.
;; Negative canonical addresses get mapped to the upper half of the 2^48 byte
;; range.
;todo: enable this less below, using rules instead?
;todo: could we instead express this as a bv-array-read 48 on the memory (converted to a bv-array)?
(defund read-byte (addr x86)
  (declare (xargs :stobjs x86
                  :guard (integerp addr)))
  (bvchop 8 (memi (bvchop 48 addr) X86)))

(defthm read-byte-when-not-integerp
  (implies (not (integerp addr))
           (equal (read-byte addr x86)
                  (read-byte 0 x86)))
  :hints (("Goal" :in-theory (enable read-byte))))

;rename to have 8 in the name?
(defthmd unsigned-byte-p-of-read-byte-simple
  (unsigned-byte-p 8 (read-byte addr x86))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm unsigned-byte-p-of-read-byte
  (implies (<= 8 size)
           (equal (unsigned-byte-p size (read-byte addr x86))
                  (natp size)))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm <=-of-read-byte-linear
  (<= (read-byte addr x86) 255)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable read-byte))))

;drop?  just for axe?
(defthmd natp-of-read-byte
  (natp (read-byte addr x86))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read-byte))))

;; maybe just needed for Axe
(defthmd <-of-read-byte-and-constant
  (implies (and (syntaxp (quotep k))
                (< 255 k) ; gets computed
                )
           (< (read-byte addr x86) k)))

;; maybe just needed for Axe
;; not used
(defthmd not-<-of-constant-and-read-byte
  (implies (and (syntaxp (quotep k))
                (<= 255 k) ; gets computed
                )
           (not (< k (read-byte addr x86)))))

(defthm read-byte-when-not-integerp-arg1-cheap
  (implies (not (integerp addr))
           (equal (read-byte addr x86)
                  (read-byte 0 x86)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable read-byte))))

; maybe drop the arg1 from the name
(defthm read-byte-of-bvchop-arg1
  (equal (read-byte (bvchop 48 addr) x86)
         (read-byte addr x86))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm read-byte-of-ifix
  (equal (read-byte (ifix ad) x86)
         (read-byte ad x86))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm read-byte-of-logext
  (implies (and (<= 48 size)
                (integerp size))
           (equal (read-byte (logext size addr) x86)
                  (read-byte addr x86)))
  :hints (("Goal" :in-theory (enable read-byte))))

;rename
(defthm read-byte-equal-when-bvchops-equal
  (implies (equal (bvchop 48 ad1) (bvchop 48 ad2))
           (equal (equal (read-byte ad1 x86) (read-byte ad2 x86))
                  t))
  :hints (("Goal" :use ((:instance read-byte-of-bvchop-arg1 (addr ad1))
                        (:instance read-byte-of-bvchop-arg1 (addr ad2)))
           :in-theory (disable read-byte-of-bvchop-arg1))))

;or do we want to introduce bvchop?
(defthm read-byte-of-+-of-bvchop-arg1
  (implies (and (integerp x)
                (integerp y))
           (equal (read-byte (+ x (bvchop 48 y)) x86)
                  (read-byte (+ x y) x86))))

;or do we want to introduce bvchop?
(defthm read-byte-of-+-of-bvchop-arg2
  (implies (and (integerp x)
                (integerp y))
           (equal (read-byte (+ (bvchop 48 y) x) x86)
                  (read-byte (+ y x) x86))))

(defthm read-byte-subst-term-arg1
  (implies (and (equal (bvchop 48 ad) (bvchop 48 free))
                (syntaxp (acl2::smaller-termp free ad)))
           (equal (read-byte ad x86)
                  (read-byte free x86)))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm read-byte-subst-term-arg1-constant
  (implies (and (equal (bvchop 48 ad) free)
                (syntaxp (and (quotep free)
                              ;; avoid loops:
                              (not (quotep ad)))))
           (equal (read-byte ad x86)
                  (read-byte free x86)))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm read-byte-of-+-subst-constant-arg1
  (implies (and (equal (bvchop 48 x) freek)
                (syntaxp (and (quotep freek)
                              ;; avoid loops:
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

;; Introduces read-byte
;rename
(defthm rvm08-becomes-read-byte
  (implies (and (canonical-address-p addr)
                (x86p x86))
           (equal (mv-nth 1 (rvm08 addr x86))
                  (read-byte addr x86)))
  :hints (("Goal" :in-theory (enable read-byte rvm08 n48))))

;rename
;todo: same as read-byte-equal-when-bvchops-equal?
(defthmd read-byte-when-bvchops-agree
  (implies (equal (bvchop 48 addr)
                  (bvchop 48 addr2))
           (equal (equal (read-byte addr x86)
                         (read-byte addr2 x86))
                  t))
  :hints (("Goal" :in-theory (enable read-byte))))

;; Note that the program-at assumption we have will be about the initial x86 state,
;; which is unlikely to be the state we're reading from.  This rule deals with that.
;; add (syntaxp (quotep bytes)) ? but this is used to prove other rules below
;; todo: reorder hyps?
;; todo: or just always go to read?
(defthmd read-byte-when-program-at-gen
  (implies (and ;; find that a program is loaded in the initial state:
            (program-at paddr bytes x86-init) ;these are free vars
            ;; try to prove that the same program is loaded in the current state:
            (program-at paddr bytes x86)
            (byte-listp bytes)
            (<= paddr addr)
            (integerp addr)
;           (integerp paddr)
            (< addr (+ paddr (len bytes)))
            (canonical-address-p paddr)
            (canonical-address-p (+ -1 (len bytes) paddr))
            (app-view x86)
            (x86p x86) ;too bad
            )
           (equal (read-byte addr x86)
                  (nth (- addr paddr)
                       bytes)))
  :hints (("Goal" :use (:instance x86isa::rb-in-terms-of-nth-and-pos-eric
                                  (x86isa::paddr paddr)
                                  (x86isa::addr addr)
                                  (x86isa::bytes bytes)
                                  (x86isa::x86-init x86-init))
           :expand (rb-1 1 addr x86isa::r-w-x x86) ;(rb-1 1 addr r-w-x x86)
           :in-theory (e/d (read-byte
                            memi ;memi*
                            xr rb rb-1  n48
                            ;;PROGRAM-AT
                            app-view ;X86ISA::APP-VIEW*
                            )
                           (;mv-nth-1-of-rb-1-becomes-read
                            x86isa::rb-in-terms-of-nth-and-pos-eric
                            ;;x86isa::rb-in-terms-of-nth-and-pos-eric-gen
                            )))))

;; ;todo: move up?  may have to change the proof
;; ;; not very useful, since the state must be the same?
;; (defthmd read-byte-when-program-at
;;   (implies (and (program-at addr2 bytes x86)
;;                 (syntaxp (quotep bytes))
;;                 (< 0 (len bytes))
;;                 (byte-listp bytes)
;;                 (canonical-address-p$inline addr2)
;;                 (canonical-address-p$inline (+ -1 addr2 (len bytes)))
;;                 (<= addr2 addr)
;;                 (< (+ addr (- addr2)) (len bytes))
;;                 (integerp addr)
;;                 (integerp addr2)
;;                 (app-view x86)
;;                 (x86p x86))
;;            (equal (read-byte addr x86)
;;                   (nth (- addr addr2) bytes)))
;;   :hints (("Goal" :use (:instance read-byte-when-program-at-gen (x86-init x86) (paddr addr2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reads an N-byte chunk starting at ADDR (in little endian fashion).
;; Unlike read-bytes, this returns the value as a bit-vector.
(defund read (n addr x86)
  (declare (xargs :stobjs x86
                  :guard (and (natp n)
                              (integerp addr))))
  (if (zp n)
      0
    (let ((addr (mbe :logic (ifix addr) :exec addr)) ; treats non-integer address as 0
          )
      (bvcat (* 8 (- n 1))
             (read (- n 1) (+ 1 addr) x86)
             8
             (read-byte addr x86)))))

;; includes the n=0 case
(defthm read-when-not-posp-cheap
  (implies (not (posp n))
           (equal (read n addr x86)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable read))))

(defthm read-when-not-integerp-arg2-cheap
  (implies (not (integerp addr))
           (equal (read n addr x86)
                  (read n 0 x86)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable read))))

; just for axe
(defthmd natp-of-read
  (natp (read n addr x86)))

(defthm unsigned-byte-p-of-read
  (implies (<= (* n 8) size)
           (equal (unsigned-byte-p size (read n addr x86))
                  (natp size)))
  :hints (("Goal" :in-theory (enable read))))

(defthm <=-of-read-linear
  (implies (natp size)
           (<= (read size addr x86) (+ -1 (expt 2 (* 8 size)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable read))))

;; maybe just needed for Axe
(defthmd <-of-read-and-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (natp size)
                (< (+ -1 (expt 2 (* 8 size))) k) ; gets computed
                )
           (< (read size addr x86) k)))

;; maybe just needed for Axe
;; add not to the name
(defthmd <-of-constant-and-read
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (natp size)
                (<= (+ -1 (expt 2 (* 8 size))) k) ; gets computed
                )
           (not (< k (read size addr x86)))))


;rename since used for a read proof as well
;add -alt to name?
(local
  (defun double-write-induct-two-addrs (n addr addr2 val x86)
    (if (zp n)
        (list n addr addr2 val x86)
      (double-write-induct-two-addrs (+ -1 n)
                                     (+ 1 addr)
                                     (+ 1 addr2)
                                     (logtail 8 val)
                                     x86))))

;rename
(local
  (defthmd read-when-bvchops-agree-helper
    (implies (and (equal (bvchop 48 addr)
                         (bvchop 48 addr2))
                  (integerp addr)
                  (integerp addr2))
             (equal (equal (read n addr x86)
                           (read n addr2 x86))
                    t))
    :hints (("Goal" :induct (double-write-induct-two-addrs N ADDR addr2 VAL X86)
             :in-theory (enable read
                                acl2::bvchop-of-sum-cases
                                read-byte-when-bvchops-agree
                                bvplus)))))

(defthmd read-when-bvchops-agree
  (implies (equal (bvchop 48 addr)
                  (bvchop 48 addr2))
           (equal (equal (read n addr x86)
                         (read n addr2 x86))
                  t))
  :hints (("Goal" :in-theory (enable ifix)
           :use (:instance read-when-bvchops-agree-helper
                           (addr (ifix addr))
                           (addr2 (ifix addr2))))))

(defthm read-of-bvchop-48
  (equal (read n (bvchop 48 addr) x86)
         (read n addr x86))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree))))

(defthm read-chop-constant-address
  (implies (and (syntaxp (quotep ad))
                (not (unsigned-byte-p 48 ad)))
           (equal (read n ad x86)
                  (read n (bvchop 48 ad) x86))))

(defthm read-subst-term-arg1-constant
  (implies (and (equal (bvchop 48 ad) free)
                (syntaxp (and (quotep free)
                              (not (quotep ad)))))
           (equal (read n ad x86)
                  (read n free x86)))
  :hints (("Goal" :in-theory (enable read))))

(defthmd read-of-if
  (equal (read n addr (if test x86 x86_2))
         (if test (read n addr x86) (read n addr x86_2))))

;enable?
(defthmd read-of-1-becomes-read-byte
  (equal (read 1 addr x86)
         (read-byte addr x86))
  :hints (("Goal" :in-theory (enable read read-byte))))

;; Not sure whether we should enable this
(defthmd read-byte-becomes-read
  (equal (read-byte addr x86)
         (read 1 addr x86))
  :hints (("Goal" :in-theory (enable read))))

;; todo: same as read-of-1-becomes-read-byte
(defthmd read-becomes-read-byte
  (equal (read 1 addr x86)
         (read-byte addr x86))
  :hints (("Goal" :in-theory (enable read))))

(theory-invariant (incompatible (:rewrite read-byte-becomes-read) (:rewrite read-becomes-read-byte)))

;gen?  allow inferring a bv size for read?
(defthm ash-of-read
  (implies (natp n)
           (equal (ash (read n addr x86) 8)
                  (bvcat (* 8 n)
                         (read n addr x86)
                         8
                         0)))
  :hints (("Goal" :use (:instance acl2::ash-becomes-bvcat
                                  (x (read n addr x86))
                                  (amt 8)
                                  (xsize (* 8 n)))
           :in-theory (e/d (read) (acl2::ash-becomes-bvcat
                                   acl2::bvcat-equal-rewrite-alt
                                   acl2::bvcat-equal-rewrite))
           :do-not '(generalize eliminate-destructors))))

;; (thm
;;  (implies (unsigned-byte-p 8 x)
;;           (equal (LOGIOR x
;;                          (ASH (READ n ADDR X86)
;;                               8))
;;                  (bvcat (* 8 n)
;;                               (READ n ADDR X86)
;;                               8
;;                               x)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;(local (in-theory (disable BITOPS::UNSIGNED-BYTE-P-INDUCT))) ; put back but this is used below

;; Generalizes X86ISA::ELEM-P-OF-XR-MEM.
(defthm unsigned-byte-p-of-xr-of-mem
  (implies (and (<= 8 n)
                (integerp n))
           (unsigned-byte-p n (xr :mem i x86$a)))
  :hints (("Goal" :use (x86isa::elem-p-of-xr-mem)
           :in-theory (disable x86isa::elem-p-of-xr-mem))))

;; Introduces read
(defthm mv-nth-1-of-rb-1-becomes-read
  (implies (and (canonical-address-p base-addr)
                (implies (posp n) (canonical-address-p (+ -1 n base-addr))))
           (equal (mv-nth 1 (rb-1 n base-addr r-x x86))
                  (read n base-addr x86)))
  :hints (("Subgoal *1/2" :cases ((equal n 1))
           :expand ((RB-1 1 BASE-ADDR R-X X86)))
          ("Goal" :in-theory (e/d (read rb-1 acl2::slice-too-high-is-0-new n48 app-view read-byte rvm08)
                                  ( ;acl2::bvcat-equal-rewrite-alt acl2::bvcat-equal-rewrite
                                   ))
           :do-not '(generalize eliminate-destructors))))

;; Introduces read, but see rb-becomes-read below.
(defthm mv-nth-1-of-rb-becomes-read
  (implies (and (app-view x86)
                (canonical-address-p addr)
                (implies (posp n) (canonical-address-p (+ -1 n addr))))
           (equal (mv-nth 1 (rb n addr r-x x86))
                  (read n addr x86)))
  :hints (("Goal" :in-theory (enable rb))))

;shouldn't need this for app-view, but it supports rb-when-zp below
(defthm x86isa::las-to-pas-when-zp
  (implies (zp n)
           (equal (x86isa::las-to-pas n lin-addr x86isa::r-w-x x86)
                  (mv nil nil x86)))
  :hints (("Goal" :in-theory (enable x86isa::las-to-pas))))

(defthm rb-when-zp
  (implies (zp n)
           (equal (rb n addr r-x x86)
                  (mv nil 0 x86)))
  :hints (("Goal" :in-theory (enable rb rb-1))))

(local (include-book "kestrel/lists-light/cons" :dir :system))

(local
 (defthm len-of-rb
   (equal (len (rb n addr r-x x86))
          3)
   :hints (("Goal" :in-theory (enable rb rb-1)))))

;; could try enabled
(defthmd rb-becomes-read
  (implies (and (canonical-address-p addr)
                ;; (implies (posp n)
                (canonical-address-p (+ -1 n addr))
                ;;)
                (app-view x86))
           (equal (rb n addr r-x x86)
                  (mv nil (read n addr x86) x86)))
  :hints (("Goal" :use (len-of-rb
                        (:instance mv-nth-1-of-rb-becomes-read (addr addr))
                        (:instance x86isa::rb-returns-no-error-app-view (x86isa::addr addr))
                        (:instance x86isa::rb-returns-x86-app-view (x86isa::addr addr)))
           :expand ((mv-nth 1 (rb n addr r-x x86))
                    (mv-nth 2 (rb n addr r-x x86))
                    (mv-nth 1 (cdr (rb n addr r-x x86)))
                    (len (rb n addr r-x x86)))
           :in-theory (e/d (;rb ;rb-1
                            mv-nth
                            len
                            )
                           (;mv-nth
                            app-view
                            mv-nth-1-of-rb-becomes-read
                            x86isa::rb-returns-no-error-app-view
                            x86isa::mv-nth-2-of-rb-when-app-view ;todo: drop this
                            x86isa::rb-returns-x86-app-view
                            len-of-rb
                            acl2::len-of-cdr)))))

(defthmd rb-1-opener
  (implies (posp n)
           (equal (rb-1 n addr r-x x86)
                  (B* (((COMMON-LISP::UNLESS (CANONICAL-ADDRESS-P ADDR))
                        (MV 'RB-1 0 X86))
                       ((MV & X86ISA::BYTE0 &) ; flg0 is not used, x86 is unchanged
                        (RVM08 ADDR X86))
                       ;; ((WHEN FLG0) (MV FLG0 0 X86)) ; can never happen
                       ((MV X86ISA::REST-FLG X86ISA::REST-BYTES X86)
                        (RB-1 (1- N) (1+ ADDR) R-X X86)))
                    (MV X86ISA::REST-FLG
                        (LOGIOR X86ISA::BYTE0
                                (ASH X86ISA::REST-BYTES 8))
                        X86))))
  :hints (("Goal" :in-theory (enable rb-1))))

(defthmd read-opener
  (implies (posp n)
           (equal (read n addr x86)
                  (LET ((ADDR (MBE :LOGIC (IFIX ADDR) :EXEC ADDR)))
                     (BVCAT (* 8 (- N 1))
                            (READ (- N 1) (+ 1 ADDR) X86)
                            8 (READ-BYTE ADDR X86)))))
  :hints (("Goal" :in-theory (enable read))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rml08-becomes-read
  (implies (app-view x86)
           (equal (rml08 lin-addr r-x x86)
                  (if (canonical-address-p lin-addr) ; only one address to check in this case
                      (mv nil (read 1 lin-addr x86) x86)
                    (mv 'rb-1 0 x86))))
  :hints (("Goal" :in-theory (enable rml08 rb rb-1-opener rb-1 rvm08
                                     read read-byte))))

;; todo: unfortunate that the erp is different in the 2 error cases
;; todo: use hints like the below
(defthm rml16-becomes-read
  (implies (app-view x86)
           (equal (rml16 lin-addr r-x x86)
                  (if (canonical-address-p (+ 1 lin-addr))
                      (if (canonical-address-p lin-addr)
                          (mv nil (read 2 lin-addr x86) x86)
                        (mv 'rb-1 0 x86))
                    (mv 'rml16 0 x86))))
  :hints (("Goal" :in-theory (enable rml16 rb rb-1-opener rb-1 rvm08
                                     read read-byte))))

(defthm rml32-becomes-read
  (implies (app-view x86)
           (equal (rml32 lin-addr r-x x86)
                  (if (and (canonical-address-p (+ 3 lin-addr))
                           (canonical-address-p lin-addr))
                      (mv nil (read 4 lin-addr x86) x86)
                    (mv 'rml32 0 x86))))
  :hints (("Goal" :in-theory (e/d (rml32 rb-becomes-read)
                                  (acl2::equal-of-cons)))))

(defthm rml48-becomes-read
  (implies (app-view x86)
           (equal (rml48 lin-addr r-x x86)
                  (if (and (canonical-address-p (+ 5 lin-addr))
                           (canonical-address-p lin-addr))
                      (mv nil (read 6 lin-addr x86) x86)
                    (mv 'rml48 0 x86))))
  :hints (("Goal" :in-theory (e/d (rml48 rb-becomes-read)
                                  (acl2::equal-of-cons)))))

(defthm rml64-becomes-read
  (implies (app-view x86)
           (equal (rml64 lin-addr r-x x86)
                  (if (and (canonical-address-p (+ 7 lin-addr))
                           (canonical-address-p lin-addr))
                      (mv nil (read 8 lin-addr x86) x86)
                    (mv 'rml64 0 x86))))
  :hints (("Goal" :in-theory (e/d (rml64 rb-becomes-read)
                                  (acl2::equal-of-cons)))))

(defthm rml80-becomes-read
  (implies (app-view x86)
           (equal (rml80 lin-addr r-x x86)
                  (if (and (canonical-address-p (+ 9 lin-addr))
                           (canonical-address-p lin-addr))
                      (mv nil (read 10 lin-addr x86) x86)
                    (mv 'rml80 0 x86))))
  :hints (("Goal" :in-theory (e/d (rml80 rb-becomes-read)
                                  (acl2::equal-of-cons)))))

(defthm rml128-becomes-read
  (implies (app-view x86)
           (equal (rml128 lin-addr r-x x86)
                  (if (and (canonical-address-p (+ 15 lin-addr))
                           (canonical-address-p lin-addr))
                      (mv nil (read 16 lin-addr x86) x86)
                    (mv 'rml128 0 x86))))
  :hints (("Goal" :in-theory (e/d (rml128 rb-becomes-read)
                                  (acl2::equal-of-cons
                                   ;; mv-nth
                                   ;; ;; for speed:
                                   ;; ACL2::LOGIOR-BOUND-LINEAR-2
                                   ;; BITOPS::LOGIOR->=-0-LINEAR BITOPS::LOGIOR-<-0-LINEAR-2
                                   ;; ;; bad:
                                   ;; X86ISA::UNSIGNED-BYTE-P-WHEN-DATA-SEGMENT-DESCRIPTORBITS-P
                                   ;; X86ISA::UNSIGNED-BYTE-P-WHEN-FP-STATUSBITS-P
                                   ;; X86ISA::UNSIGNED-BYTE-P-WHEN-GDTR/IDTRBITS-P
                                   ;; X86ISA::UNSIGNED-BYTE-P-WHEN-HIDDEN-SEGMENT-REGISTERBITS-P
                                   ;; X86ISA::UNSIGNED-BYTE-P-WHEN-INTERRUPT/TRAP-GATE-DESCRIPTORBITS-P
                                   ;; X86ISA::UNSIGNED-BYTE-P-WHEN-MXCSRBITS-P
                                   )))))

(defthm rml256-becomes-read
  (implies (app-view x86)
           (equal (rml256 lin-addr r-x x86)
                  (if (and (canonical-address-p (+ 31 lin-addr))
                           (canonical-address-p lin-addr))
                      (mv nil (read 32 lin-addr x86) x86)
                    (mv 'rml256 0 x86))))
  :hints (("Goal" :in-theory (e/d (rml256 rb-becomes-read)
                                  (acl2::equal-of-cons)))))

(defthm rml512-becomes-read
  (implies (app-view x86)
           (equal (rml512 lin-addr r-x x86)
                  (if (and (canonical-address-p (+ 63 lin-addr))
                           (canonical-address-p lin-addr))
                      (mv nil (read 64 lin-addr x86) x86)
                    (mv 'rml512 0 x86))))
:hints (("Goal" :in-theory (e/d (rml512 rb-becomes-read)
                                (acl2::equal-of-cons)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rme08-of-0-when-not-fs/gs-becomes-read
  (implies (and (not (equal seg-reg *fs*))
                (not (equal seg-reg *gs*))
                (app-view x86))
           (equal (rme08 0 eff-addr seg-reg r-x x86) ; 0 means 64-bit-mode
                  (if (canonical-address-p eff-addr)
                      (mv nil (read 1 eff-addr x86) x86)
                    (mv (list :non-canonical-address eff-addr) 0 x86))))
  :hints (("Goal" :in-theory (e/d (rme08) (rml08)))))

;; ;; Just the reverse of the above
;; (defthmd read-becomes-mv-nth-1-of-rb
;;   (implies (and (app-view x86)
;;                 (x86p x86)
;;                 (canonical-address-p addr)
;;                 (implies (posp n) (canonical-address-p (+ -1 n addr))))
;;            (equal (read n addr x86)
;;                   (mv-nth 1 (rb n addr r-x x86))))
;;   :hints (("Goal" :by mv-nth-1-of-rb-becomes-read)))

;; ;; Introduces read
;; (defthmd memi-becomes-read-1
;;   (implies (x86p x86)
;;            (equal (memi (bvchop 48 addr) x86)
;;                   (read 1 addr x86)))
;;   :hints (("Goal" :in-theory (enable read read-byte))))

;; ;; Introduces read
;; (defthmd memi-becomes-read-2
;;   (implies (and (x86p x86)
;;                 (integerp addr)
;;                 (integerp n))
;;            (equal (memi (bvplus 48 n addr) x86)
;;                   (read 1 (+ n addr) x86)))
;;   :hints (("Goal" :in-theory (enable read bvplus read-byte))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; "simple" because there is only one state var
(defthm read-when-program-at-1-byte-simple
  (implies (and (program-at paddr bytes x86) ; paddr and bytes are free vars
                (<= paddr addr)
                (< (- addr paddr) (len bytes))
                (byte-listp bytes) ; todo: inefficient?  is there another byte-listp?
                (integerp addr)
                ;; (integerp paddr)
                (canonical-address-p paddr)
                (canonical-address-p (+ -1 (len bytes) paddr))
                (app-view x86)
                (x86p x86) ;too bad
                )
           (equal (read 1 addr x86)
                  (nth (- addr paddr)
                       bytes)))
  :hints (("Goal" :in-theory (enable read read-byte-when-program-at-gen))))

;; Note that the program-at assumption we have will be about the initial x86 state,
;; which is unlikely to be the state we're reading from.  This rule deals with that.
;; todo: why wouldn't we be able to simplify the read until it is reading from the initial state var?
(defthm read-when-program-at-1-byte
  (implies (and ;; find that a program is loaded in the initial state:
            (program-at paddr bytes x86-init) ;these are free vars
            (<= paddr addr)
            (< (- addr paddr) (len bytes))
            ;; try to prove that the same program is loaded in the current state:
            (program-at paddr bytes x86)
            (byte-listp bytes)
            (integerp addr)
            ;; (integerp paddr)
            (canonical-address-p paddr)
            (canonical-address-p (+ -1 (len bytes) paddr))
            (app-view x86)
            (x86p x86) ;too bad
            )
           (equal (read 1 addr x86)
                  (nth (- addr paddr)
                       bytes)))
  :hints (("Goal" :in-theory (enable read read-byte-when-program-at-gen))))

;todo: gen
(defthm read-when-program-at-2-bytes
  (implies (and (program-at paddr bytes x86-init)
                (<= paddr addr)
                (< (- addr paddr) (+ -1 (len bytes)))
                (program-at paddr bytes x86)
                (byte-listp bytes)
                (integerp addr)
                (canonical-address-p paddr)
                (canonical-address-p (+ -1 (len bytes) paddr))
                (app-view x86)
                (app-view x86-init)
                (x86p x86))
           (equal (read 2 addr x86)
                  (acl2::bvcat2 8 (nth (+ 1 addr (- paddr)) bytes)
                                8 (nth (+ addr (- paddr)) bytes))))
  :hints (("Goal" :in-theory (enable read read-byte-when-program-at-gen)
           :expand ((read 2 (+ 2 addr) x86)))))

;todo: gen
(defthm read-when-program-at-4-bytes
  (implies (and (program-at paddr bytes x86-init)
                (<= paddr addr)
                (< (- addr paddr) (+ -3 (len bytes)))
                (program-at paddr bytes x86)
                (byte-listp bytes)
                (integerp addr)
                (canonical-address-p paddr)
                (canonical-address-p (+ -1 (len bytes) paddr))
                (app-view x86)
                (app-view x86-init)
                (x86p x86))
           (equal (read 4 addr x86)
                  (acl2::bvcat2 8 (nth (+ 3 addr (- paddr)) bytes)
                                8 (nth (+ 2 addr (- paddr)) bytes)
                                8 (nth (+ 1 addr (- paddr)) bytes)
                                8 (nth (+ addr (- paddr)) bytes))))
  :hints (("Goal" :in-theory (enable read read-byte-when-program-at-gen)
           :expand ((read 4 addr x86)
                           (read 3 (+ 1 addr) x86)
                           (read 2 (+ 2 addr) x86)))))

(defthm read-when-program-at-8-bytes
  (implies (and (program-at paddr bytes x86-init)
                (<= paddr addr)
                (< (- addr paddr) (+ -7 (len bytes)))
                (program-at paddr bytes x86)
                (byte-listp bytes)
                (integerp addr)
                (canonical-address-p paddr)
                (canonical-address-p (+ -1 (len bytes) paddr))
                (app-view x86)
                (app-view x86-init)
                (x86p x86))
           (equal (read 8 addr x86)
                  (acl2::bvcat2 8 (nth (+ 7 addr (- paddr)) bytes)
                                8 (nth (+ 6 addr (- paddr)) bytes)
                                8 (nth (+ 5 addr (- paddr)) bytes)
                                8 (nth (+ 4 addr (- paddr)) bytes)
                                8 (nth (+ 3 addr (- paddr)) bytes)
                                8 (nth (+ 2 addr (- paddr)) bytes)
                                8 (nth (+ 1 addr (- paddr)) bytes)
                                8 (nth (+ addr (- paddr)) bytes))))
  :hints (("Goal" :in-theory (enable read read-byte-when-program-at-gen)
           :expand ((read 8 addr x86)
                           (read 7 (+ 1 addr) x86)
                           (read 6 (+ 2 addr) x86)
                           (read 5 (+ 3 addr) x86)
                           (read 4 (+ 4 addr) x86)
                           (read 3 (+ 5 addr) x86)
                           (read 2 (+ 6 addr) x86)))))

;; Often N and PADDR and BYTES are constants
;(include-book "kestrel/bv-lists/packbv-little" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read-chunk-little" :dir :system)
(local (include-book "kestrel/bv-lists/packbv-theorems" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
;todo: delete the specializations above..
;drop any hyps?
;todo: if we can't resolve the index, something like bv-array-read might be preferable.  but we would need multi-byte reads...
;rename
;compare to read-when-program-at-8-bytes, etc.
(defthm read-when-program-at
  (implies (and (program-at paddr bytes x86)
                (<= paddr addr)
                ;; We expect any common addends in ADDR and PADDR to be removed when simplifying the difference, (+ addr (- paddr)).
                ;; And we expect the term (+ 1 (- n) (len bytes)) to often be ground:
                (< (+ addr (- paddr)) (+ 1 (- n) (len bytes)))
                (canonical-address-p paddr)
                (canonical-address-p (+ -1 (len bytes) paddr))
                ;;(program-at paddr bytes x86-init)
                ;;(program-at paddr bytes x86) ; ensure the bytes are still present (todo: might not be needed if we apply this rule last)
                (byte-listp bytes) ; drop?
                (integerp addr)
                (app-view x86)
                ;; (app-view x86-init)
                (x86p x86))
           (equal (read n addr x86)
                  ;; todo: consider what should happen here if ADDR is not a constant:
                  ;;(acl2::packbv-little n 8 (take n (nthcdr (- addr paddr) bytes)))
                  (bv-array-read-chunk-little n 8 (len bytes) (- addr paddr) bytes)))
  :hints (("Goal" :in-theory (e/d (read
                                   read-byte-when-program-at-gen
                                   acl2::bv-array-read-chunk-little
                                   ;;acl2::packbv-little ; todo
                                   bv-array-read)
                                  (true-listp)))))

;(def-constant-opener acl2::packbv-little) ; move?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(local
  (defun read-induct (low n addr)
    (if (zp n)
        (list low n addr)
      (read-induct (+ -1 low) (+ -1 n) (+ 1 addr)))))

;rename ...read-1
(defthm slice-of-read-one-byte
  (implies (and (natp low)
                (integerp addr)
                (natp n)
                (< low n))
           (equal (acl2::slice (+ 7 (* 8 low)) (* 8 low) (read n addr x86))
                  (read 1 (+ low addr) x86)))
  :hints (("Goal" :induct (read-induct low n addr)
           :in-theory (enable read read-byte))))

(defthm slice-of-read-one-byte-gen
  (implies (and (syntaxp (and (quotep low)
                              (quotep high)))
                (equal 0 (mod low 8))
                (equal high (+ 7 low))
                (integerp addr)
                (< (/ low 8) n)
                (natp low)
                (natp n))
           (equal (acl2::slice high low (read n addr x86))
                  (read 1 (+ (/ low 8) addr) x86)))
  :hints (("Goal" :use (:instance slice-of-read-one-byte
                                  (low (/ low 8)))
           :in-theory (disable slice-of-read-one-byte))))

(local (include-book "kestrel/arithmetic-light/integerp" :dir :system))

(local
  (defun bvchop-of-read-induct (numbits numbytes addr)
    (if (zp numbytes)
        (list numbits numbytes addr)
      (bvchop-of-read-induct (+ -8 numbits) (+ -1 numbytes) (+ 1 (ifix addr))))))

(defthm bvchop-of-read
  (implies (and (equal 0 (mod numbits 8))
                (natp numbits)
                (natp numbytes))
           (equal (bvchop numbits (read numbytes addr x86))
                  (if (< numbits (* 8 numbytes))
                      (read (/ numbits 8) addr x86)
                    (read numbytes addr x86))))
  :hints (("Goal" :induct (bvchop-of-read-induct numbits numbytes addr)
           :expand (read numbytes addr x86)
           :in-theory (enable READ))))

(local
  (defun read-high-low-induct (n addr x86 high low)
    (declare (xargs :stobjs x86
                    :verify-guards nil))
    (if (zp n)
        (mv n addr x86 high low)
      (read-high-low-induct (- n 1) (+ 1 addr) x86 (+ -8 high) (+ -8 low)))))

;for whole bytes
;move up
(defthm slice-of-read
  (implies (and ;; (syntaxp (and (quotep low)
                ;;               (quotep high)))
                (equal 0 (mod low 8)) ; low bit of some byte
                ;;(equal 7 (mod high 8)) ; high bit of some byte
                (integerp (/ (+ high 1) 8))
                (< high (* 8 n))
;                (<= low high)
                (natp low)
                (natp high)
                (natp n)
                (integerp addr))
           (equal (slice high low (read n addr x86))
                  (read (/ (+ 1 high (- low)) 8) ; number if bytes to read
                        (+ (/ low 8) ; number of bytes we skip
                           addr)
                        x86)))
  :hints (("subgoal *1/2" :cases ((< high 7)))
          ("Goal" :induct (read-high-low-induct n addr x86 high low)
           :do-not '(generalize eliminate-destructors)
           :expand (read (+ 1/8 (* 1/8 high)) addr x86)
           :in-theory (e/d (read acl2::integerp-squeeze)
                           (acl2::<=-of-*-and-*-same-linear
                            acl2::<=-of-*-and-*-same-alt-linear
                            ;; these seemed to add stuff to the goal itself?!  why?
                            acl2::<-of-*-and-*-same-forward-1
                            acl2::<-of-*-and-*-same-forward-2
                            acl2::<-of-*-and-*-same-forward-3
                            acl2::<-of-*-and-*-same-forward-4)))))

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
                  ;; or go to bv-array-read, in case the indexing can't be resolved?
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

;todo: just drop the bvchop?
(defthm read-of-bvchop-tighten
  (implies (and (syntaxp (quotep size))
                (< 48 size)
                (integerp size))
           (equal (read n (bvchop size addr) x86)
                  (read n (bvchop 48 addr) x86)))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree))))

(defthm read-of-bvplus-tighten
  (implies (and (syntaxp (quotep size))
                (< 48 size)
                (integerp size))
           (equal (read n (bvplus size x y) x86)
                  (read n (bvplus 48 x y) x86)))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree))))

;; we use logext so that negative constants are nice
(defthm read-of-bvplus-normalize
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (integerp addr))
           (equal (read n (bvplus 48 k addr) x86)
                  (read n (+ (logext 48 k) addr) x86)))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree
                                     acl2::bvchop-of-+-becomes-bvplus))))


;; or do we want bvplus?
(defthm read-of-bvplus
  (implies (and (integerp x)
                (integerp y))
           (equal (read n (bvplus 48 x y) x86)
                  (read n (+ x y) x86)))
 :hints (("Goal" :in-theory (enable read-when-bvchops-agree
                                    acl2::bvchop-of-+-becomes-bvplus))))

;; opposite of read-of-bvplus
(defthmd read-of-+-arg2
  (implies (and (integerp x)
                (integerp y))
           (equal (read n (+ x y) x86)
                  (read n (bvplus 48 x y) x86)))
  :hints (("Goal" :in-theory (e/d (read) (READ-OF-BVPLUS-TIGHTEN ; todo loop
                                          ;ACL2::BVPLUS-COMMUTATIVE-2-SIZES-DIFFER
                                          )))))

(theory-invariant (incompatible (:rewrite read-of-+-arg2) (:rewrite read-of-bvplus)))

(defthm read-of-+-of-expt ; gen the 48?
  (implies (integerp addr)
           (equal (read n (+ addr (expt 2 48)) x86)
                  (read n addr x86)))
  :hints (("Goal" :in-theory (enable read))))

(defthm read-of-+-normalize
  (implies (and (syntaxp (quotep k))
                (not (signed-byte-p 48 k))
                (integerp k)
                (integerp x))
           (equal (read n (+ k x) x86)
                  (read n (+ (logext 48 k) x) x86)))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree
                                     acl2::bvchop-of-+-becomes-bvplus))))

(defthm read-of-+-of-bvplus
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (read n (+ x (bvplus 48 y z)) x86)
                  (read n (+ x y z) x86)))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree
                                     acl2::bvchop-of-+-becomes-bvplus))))

(defthm read-of-+-of-bvplus-alt
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (read n (+ (bvplus 48 y z) x) x86)
                  (read n (+ y z x) x86)))
  :hints (("Goal" :in-theory (enable read-when-bvchops-agree
                                     acl2::bvchop-of-+-becomes-bvplus))))

;; Only needed for Axe
(defthmd integerp-of-read
  (integerp (read n addr x86)))

;rename
(defthm <-of-read-and-non-positive
  (implies (and (syntaxp (quotep k))
                (<= k 0))
           (equal (< (read n adr x86) k)
                  nil)))

;; Splits into individual reads, which then get resolved
;; TODO: Instead, resolve a read of 2 bytes when we have an appropriate program-at claim
(defthm read-2-blast
  (equal (read 2 addr x86)
         (bvcat 8 (read 1 (+ 1 (ifix addr)) x86) ; todo: or use bvplus?
                8 (read 1 addr x86)))
  :hints (("Goal" :in-theory (enable read))))

;drop?
;; (defthmd equal-of-read-and-read-helper
;;   (implies (and (equal (bvchop 48 addr1) (bvchop 48 addr2))
;;                 (integerp addr1)
;;                 (integerp addr2))
;;            (equal (equal (read n addr1 x86)
;;                          (read n addr2 x86))
;;                   t))
;;   :hints (("Goal" :in-theory (enable read))))

(defthm read-of-logext
  (implies (and (<= 48 size)
                (integerp size)
                (integerp addr) ;drop?
                )
           (equal (read n (logext size addr) x86)
                  (read n addr x86)))
  :hints (("Goal" :cases ((integerp addr))
           :in-theory (enable read-when-bvchops-agree))))

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
           :in-theory (enable read bvplus))))

;; This variant uses + instead of bvplus
(defthmd read-4-blast-alt
  (implies (integerp addr)
           (equal (read 4 addr x86)
                  (bvcat 8
                         (read 1 (+ 3 addr) x86)
                         24
                         (bvcat 8
                                (read 1 (+ 2 addr) x86)
                                16
                                (bvcat 8
                                       (read 1 (+ 1 addr) x86)
                                       8
                                       (read 1 addr x86))))))
  :hints (("Goal" :use (:instance read-4-blast))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm trim-of-read
  (implies (and (equal 0 (mod numbits 8)) ; todo: gen?
                (natp numbits)
                (natp numbytes))
           (equal (acl2::trim numbits (read numbytes addr x86))
                  (if (< numbits (* 8 numbytes))
                      (read (/ numbits 8) addr x86)
                    (read numbytes addr x86))))
  :hints (("Goal" :in-theory (enable acl2::trim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; where should these go?
(defthm svblt-of-read-trim-arg2
  (implies (and (< size (* 8 n))
                (posp size))
           (equal (sbvlt size (read n addr x86) y)
                  (sbvlt size (acl2::trim size (read n addr x86)) y)))
  :hints (("Goal" :in-theory (enable acl2::trim))))

(defthm svblt-of-read-trim-arg3
  (implies (and (< size (* 8 n))
                (posp size))
           (equal (sbvlt size y (read n addr x86))
                  (sbvlt size y (acl2::trim size (read n addr x86)))))
  :hints (("Goal" :in-theory (enable acl2::trim))))

(local (include-book "kestrel/arithmetic-light/limit-expt" :dir :system))

;move up
(defthm read-of-+-bvchop-arg2
  (implies (and (integerp k)
                (integerp ad))
           (equal (read n (+ k (bvchop 48 ad)) x86)
                  (read n (+ k ad) x86)))
  :hints (("Goal" :use ((:instance read-of-bvchop-48 (addr (+ k (bvchop 48 ad))))
                        (:instance read-of-bvchop-48 (addr (+ k ad))))
           :in-theory (disable read-of-bvchop-48))))

(defthm read-of-+-subst-arg2
  (implies (and (equal (bvchop 48 ad) free)
                (syntaxp (acl2::smaller-termp free ad))
                (integerp k)
                (integerp ad))
           (equal (read n (+ k ad) x86)
                  (read n (+ k free) x86))))

(defthm bvchop-8-of-read
  (implies (posp n)
           (equal (bvchop 8 (read n addr x86))
                  (read 1 addr x86)))
  :hints (("Goal" :in-theory (enable read))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;
;; write-byte
;;

;; Writes the BYTE at address ADDR.
(defund write-byte (addr byte x86)
  (declare (xargs :stobjs x86
                  :guard (and (acl2::unsigned-byte-p 8 byte)
                              (integerp addr))))
  (!memi (bvchop 48 addr)
         (bvchop 8 byte)
         X86))

(defthm write-byte-when-not-integerp
  (implies (not (integerp addr))
           (equal (write-byte addr byte x86)
                  (write-byte 0 byte x86)))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm write-byte-of-bvchop-arg2
  (equal (write-byte ad (bvchop 8 val) x86)
         (write-byte ad val x86))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm write-byte-of-+-bvchop-arg2
  (implies (and (integerp n)
                (integerp ad))
           (equal (write-byte (+ n (bvchop 48 ad)) val x86)
                  (write-byte (+ n ad) val x86)))
  :hints (("Goal" :in-theory (enable write-byte))))


(defthm write-byte-of-bvchop-arg1
  (equal (write-byte (bvchop 48 ad) byte x86)
         (write-byte ad byte x86))
  :hints (("Goal"
           :in-theory (enable write-byte))))

(defthm write-byte-of-write-byte-same
  (implies (integerp ad)
           (equal (write-byte ad byte1 (write-byte ad byte2 x86))
                  (write-byte ad byte1 x86)))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm write-byte-of-ifix
  (equal (write-byte (ifix ad) val x86)
         (write-byte ad val x86))
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
  :hints (("Goal" :in-theory (enable write-byte
                                     !memi ; todo
                                     ))))

(defthm write-byte-of-write-byte-gen
  (implies (and (syntaxp (acl2::smaller-termp ad2 ad1))
                (integerp ad1)
                (integerp ad2))
           (equal (write-byte ad1 byte1 (write-byte ad2 byte2 x86))
                  (if (equal (bvchop 48 ad1)
                             (bvchop 48 ad2))
                      (write-byte ad1 byte1 x86)
                    (write-byte ad2 byte2 (write-byte ad1 byte1 x86)))))
  :hints (("Goal" :in-theory (enable write-byte
                                     !memi ; todo
                                     ))))

(defthmd xw-becomes-write-byte
  (implies (and (acl2::unsigned-byte-p 8 byte)
                (unsigned-byte-p 48 addr)
                (integerp addr))
           (equal (xw :mem addr byte x86)
                  (write-byte addr byte x86)))
  :hints (("Goal" :in-theory (enable write-byte !memi))))

(defthm write-byte-equal-when-bvchops-equal
  (implies (and (equal (bvchop 48 ad1) (bvchop 48 ad2))
                (integerp ad1)
                (integerp ad2))
           (equal (equal (write-byte ad1 byte x86) (write-byte ad2 byte x86))
                  t))
  :hints (("Goal" :use ((:instance write-byte-of-bvchop-arg1
                                   (ad ad1)
                                   (byte byte))
                        (:instance write-byte-of-bvchop-arg1
                                   (ad ad2)
                                   (byte byte)))
           :in-theory (disable write-byte-of-bvchop-arg1))))

(defthm write-byte-of-+-subst-arg1
  (implies (and (equal (bvchop 48 ad) freek)
                (syntaxp (and (quotep freek) (not (quotep ad))))
                (integerp ad)
                (integerp freek))
           (equal (write-byte (+ 1 ad) byte x86)
                  (write-byte (+ 1 freek) byte x86))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;
;; Rules about read-byte and write-byte
;;

;; Could weaken to just require the bvchops to be equal
(defthm read-byte-of-write-byte-same
  (equal (read-byte addr (write-byte addr byte x86))
         (bvchop 8 byte))
  :hints (("Goal" :in-theory (enable read-byte write-byte))))

(defthm read-byte-of-write-byte-diff
  (implies (not (equal (bvchop 48 addr1)
                       (bvchop 48 addr2)))
           (equal (read-byte addr1 (write-byte addr2 byte x86))
                  (read-byte addr1 x86)))
  :hints (("Goal" :in-theory (enable read-byte write-byte))))

;; Handles both cases (same address, different address).
;; Could add separate -same and -diff rules that would not cause case splits.
(defthm read-byte-of-write-byte
  (equal (read-byte addr1 (write-byte addr2 byte x86))
         (if (equal (bvchop 48 addr1)
                    (bvchop 48 addr2))
             (bvchop 8 byte)
           (read-byte addr1 x86)))
  :hints (("Goal" :in-theory (enable read-byte write-byte))))

;; Writing the byte that is already there does nothing
(defthm write-byte-of-read-byte-same
  (equal (write-byte addr (read-byte addr x86) x86)
         x86)
  :hints (("Goal" :in-theory (enable read-byte write-byte
                                     memi !memi
                                     ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Writes the N-byte chunk VAL starting at ADDR (in little endian fashion).
(defund write (n addr val x86)
  (declare (xargs :stobjs x86
                  :guard (and (natp n)
                              (unsigned-byte-p (* 8 n) val)
                              (integerp addr))))
  (if (zp n)
      x86
    (let ((x86 (write-byte addr (bvchop 8 val) X86)))
      (write (+ -1 n)
             (+ 1 (mbe :logic (ifix addr) :exec addr))
             (logtail 8 val) ;(slice (+ -1 (* 8 n)) 8 val)
             x86))))

(defthm write-of-0
  (equal (write 0 ad val x86)
         x86)
  :hints (("Goal" :in-theory (enable write))))

(defthm write-when-not-posp
  (implies (not (posp n))
           (equal (write n ad val x86)
                  x86))
  :hints (("Goal" :in-theory (enable write))))

(defthm write-when-not-integerp
  (implies (not (integerp ad))
           (equal (write n ad val x86)
                  (write n 0 val x86)))
  :hints (("Goal" :in-theory (enable write))))

(defthmd write-of-1-becomes-write-byte
  (equal (write 1 addr val x86)
         (write-byte addr val x86))
  :hints (("Goal" :in-theory (enable write))))

(defthmd write-byte-becomes-write-of-1
  (equal (write-byte addr val x86)
         (write 1 addr val x86))
  :hints (("Goal" :in-theory (enable write))))

(theory-invariant (incompatible (:rewrite write-of-1-becomes-write-byte) (:rewrite write-byte-becomes-write-of-1)))

(local
  (defun-nx double-write-induct-two-addrs2 (n addr addr2 val x86)
    (if (zp n)
        (list n addr addr2 val x86)
      (double-write-induct-two-addrs2 (+ -1 n)
                                      (+ 1 addr)
                                      (+ 1 addr2)
                                      (logtail 8 val)
                                      (XW :MEM (BVCHOP 48 addr)
                                          (BVCHOP 8 VAL)
                                          X86)))))

;rename
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
           :in-theory (enable write write-byte acl2::bvchop-of-sum-cases !memi))))

; gen the 48
(defthm write-of-bvchop-48
  (implies (integerp addr)
           (equal (write n (bvchop 48 addr) val x86)
                  (write n addr val x86)))
  :hints (("Goal" :use (:instance write-when-bvchops-agree
                                  (addr2 (bvchop 48 addr))
                                  (addr addr)))))

(defthm write-of-bvchop-tighten
  (implies (and (syntaxp (quotep size))
                (< 48 size)
                (integerp size))
           (equal (write n (bvchop size addr) val x86)
                  (write n (bvchop 48 addr) val x86)))
  :hints (("Goal" :in-theory (enable write-when-bvchops-agree))))

(defthm write-of-+-bvchop-arg2
  (implies (and (integerp k)
                (integerp ad))
           (equal (write n (+ k (bvchop 48 ad)) val x86)
                  (write n (+ k ad) val x86)))
  :hints (("Goal" :use ((:instance write-of-bvchop-48 (addr (+ k (bvchop 48 ad))))
                        (:instance write-of-bvchop-48 (addr (+ k ad))))
           :in-theory (disable write-of-bvchop-48))))

(defthm write-of-+-subst-arg2
  (implies (and (equal (bvchop 48 ad) free)
                (syntaxp (acl2::smaller-termp free ad))
                (integerp k)
                (integerp ad))
           (equal (write n (+ k ad) val x86)
                  (write n (+ k free) val x86))))

(defthm write-of-bvplus-tighten
  (implies (and (syntaxp (quotep size))
                (< 48 size)
                (integerp size))
           (equal (write n (bvplus size x y) val x86)
                  (write n (bvplus 48 x y) val x86)))
  :hints (("Goal" :in-theory (enable write-when-bvchops-agree))))

(defthm write-of-logext-arg2
  (implies (and (<= 48 size)
                (integerp size))
           (equal (write n (logext size addr) val x86)
                  (write n addr val x86)))
  :hints (("Goal" :use (write-of-bvchop-48
                         (:instance write-of-bvchop-48 (addr (logext size addr))))
           :in-theory (disable write-of-bvchop-48))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm mv-nth-0-of-wb-1
  (implies (and (posp n)
                (app-view x86)
                )
           (equal (mv-nth 0 (wb-1 n addr w value x86))
                  (if (and (canonical-address-p addr)
                           (canonical-address-p (+ -1 n addr)))
                      nil
                    t)))
  :hints (("Goal" :in-theory (enable wb-1))))

;; Introduces WRITE.
(defthm mv-nth-1-of-wb-1-becomes-write
  (implies (and (app-view x86)
                (canonical-address-p addr)
                ;; (implies (posp n)
                (canonical-address-p (+ -1 n addr)) ; not good for n=0
                ;;)
                )
           (equal (mv-nth 1 (wb-1 n addr w value x86))
                  (write n addr value x86)))
  :hints (("Subgoal *1/3" :cases ((equal n 1)))
          ("Goal" :in-theory (e/d (wb-1 wvm08 acl2::slice-too-high-is-0-new n48 write write-byte)
                                  ( ;acl2::bvcat-equal-rewrite-alt acl2::bvcat-equal-rewrite
                                   ))
           :induct (wb-1 n addr w value x86)
           :expand ((write n addr value x86)
                    (wb-1 1 addr w value x86)
                    (write 1 addr value x86))
           :do-not '(generalize eliminate-destructors))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Introduces WRITE.
(defthm mv-nth-1-of-wb-becomes-write-when-app-view
  (implies (and (app-view x86)
                (canonical-address-p addr)
                ;; (implies (posp n)
                (canonical-address-p (+ -1 n addr)) ; not good for n=0
                ;;)
                )
           (equal (mv-nth 1 (wb n addr w value x86))
                  (write n addr value x86)))
  :hints (("Goal" :in-theory (e/d (wb app-view)
                                  (wb-1 write)))))

(defthm mv-nth-0-of-wb-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 0 (wb n addr w value x86))
                  (if (or (zp n)
                          (and (canonical-address-p addr)
                               (canonical-address-p (+ -1 n addr))))
                      nil
                    t)))
  :hints (("Goal" :in-theory (enable wb))))

;; This alias supports our strategy to move hyps to the RHSes of rules, even
;; when there is no clear simplification available in the cases where the
;; hyps are not (all) true.  If wb-alias appears in a failed proof/lift,
;; look for canonical-address-p terms that did not get simplified.
(defun-nx wb-alias (n addr w value x86)
  (wb n addr w value x86))

(in-theory (disable wb-alias))

(local
  (defthm wb-when-zp
    (implies (zp n)
             (equal (wb n addr w value x86)
                    (mv nil x86)))
    :hints (("Goal" :in-theory (enable wb)))))

(local
  (defthm wb-alias-when-zp
    (implies (zp n)
             (equal (wb-alias n addr w value x86)
                    (mv nil x86)))
    :hints (("Goal" :in-theory (enable wb-alias)))))

(local
  (defthm len-of-wb
    (equal (len (wb n addr w value x86))
           2)
    :hints (("Goal" :in-theory (enable wb)))))

(local
  (defthm cddr-of-wb
    (equal (cddr (wb n addr w value x86))
           nil)
    :hints (("Goal" :in-theory (enable wb)))))

;; This puts the canonical-address-p claims in the RHS.  Since there is not a
;; convenient way to specify what happens in the non-canonical cases, we put in
;; the alias.
(defthm wb-becomes-write-when-app-view
  (implies (app-view x86)
           (equal (wb n addr w value x86)
                  (if (or (zp n)
                          (and (canonical-address-p addr)
                               (canonical-address-p (+ -1 n addr))))
                      (mv nil (write n addr value x86))
                    ;; this case should not happen:
                    (wb-alias n addr w value x86))))
  :hints (("Goal" :use (mv-nth-1-of-wb-becomes-write-when-app-view
                        mv-nth-0-of-wb-when-app-view)
           :expand (mv-nth 1 (wb n addr w value x86))
           :in-theory (e/d (wb-alias mv-nth)
                           (mv-nth-0-of-wb-when-app-view ;acl2::equal-of-cons
                            mv-nth-1-of-wb-becomes-write-when-app-view
                            x86isa::wb-by-wb-1-for-app-view-induction-rule)))))

(theory-invariant (incompatible (:rewrite wb-becomes-write-when-app-view) (:definition wb-alias)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; or turn the xw into a write
(defthmd write-of-xw-mem
  (implies (and (< n (bvchop 48 (- addr addr2))) ;no wrap around ;(< (bvchop 48 addr) (bvchop 48 addr2))
                (integerp addr2)
                (integerp addr))
           (equal (write n addr2 val2 (xw :mem addr val x86))
                  (xw :mem addr val (write n addr2 val2 x86))))
  :hints (("Subgoal *1/3" :cases ((equal n 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (WRITE N ADDR2 VAL2 X86)
           :in-theory (enable write
                              ACL2::BVCHOP-PLUS-1-SPLIT
                              ACL2::BVCHOP-OF-SUM-CASES
                              write-byte
                              memi !memi  ;todo
                              )
           :expand ((:free (addr val x86) (WRITE 1 ADDR VAL X86))
                    (:free (addr val x86) (WRITE n ADDR VAL X86))))))


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
           :in-theory (e/d (write separate write-byte acl2::equal-of-bvchop-and-bvchop)
                           ()))))

(defthm xr-of-write-too-low
  (implies (and (< addr1 addr2)
        ;        (natp n)
                (integerp addr1)
                (integerp addr2)
;                (< N 281474976710656)
 ;               (canonical-address-p addr1)
                (canonical-address-p addr2)
                (implies (posp n) (canonical-address-p (+ -1 n addr2)))
                )
           (equal (xr :mem addr1 (write n addr2 val x86))
                  (xr :mem addr1 x86)))
  :hints (("Goal" :in-theory (enable write CANONICAL-ADDRESS-P write-byte
                                     WRITE-OF-XW-MEM))))

;use bvlt?
(defthm xr-of-write-too-low-alt
  (implies (and (< (bvchop 48 addr1) (bvchop 48 addr2))
;                (natp n)
                (<= (+ n addr2) (expt 2 48)) ;gen?
                (unsigned-byte-p 48 addr1)
                (unsigned-byte-p 48 addr2))
           (equal (xr :mem addr1 (write n addr2 val x86))
                  (xr :mem addr1 x86)))
  :hints (("Goal" :in-theory (enable write write-byte))))

(defthm xr-of-write-too-high-alt
  (implies (and (< (+ n addr2) addr1)
;                (natp n)
;                (< (+ n addr2) (expt 2 48)) ;gen?
                (unsigned-byte-p 48 addr1)
                (unsigned-byte-p 48 addr2))
           (equal (xr :mem addr1 (write n addr2 val x86))
                  (xr :mem addr1 x86)))
  :hints (("Goal" :in-theory (enable write write-byte))))

; use bvle?
;add mem to the name
(defthm xr-of-write-irrel
  (implies (and (<= n (bvchop 48 (- addr1 addr2))) ; todo: use bvminus
                (integerp addr1)
                (integerp addr2))
           (equal (xr :mem addr1 (write n addr2 val x86))
                  (xr :mem addr1 x86)))
  :hints (("Goal" :induct (write n addr2 val x86)
           :in-theory (enable write write-byte canonical-address-p bvplus acl2::bvchop-of-sum-cases))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO make a version of separate without the r-w-x stuff and that handles wrap-around??  see disjoint-regionsp

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

;mixes abstraction levels - todo remove -- or make local?
(defthm memi-of-write-byte-same
  (implies (unsigned-byte-p 48 addr)
           (equal (memi addr (write-byte addr byte x86))
                  (bvchop 8 byte)))
  :hints (("Goal" :in-theory (enable write-byte))))

;mixes abstraction levels - todo remove?
(defthm memi-of-write-byte-diff
  (implies (not (equal (bvchop 48 addr1)
                            (bvchop 48 addr2)))
           (equal (memi addr1 (write-byte addr2 byte x86))
                  (memi addr1 x86)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable write-byte memi))))

;mixes abstraction levels - todo remove?
(defthmd memi-of-write-byte
  (implies (and ;(integerp addr1)
                (unsigned-byte-p 48 addr1)
                ;(integerp addr2)
                )
           (equal (memi addr1 (write-byte addr2 byte x86))
                  (if (equal (bvchop 48 addr1)
                             (bvchop 48 addr2))
                      (bvchop 8 byte)
                    (memi addr1 x86))))
    :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable write-byte memi))))

(defthm memi-of-bvchop-and-write
  (implies (and (or (<= (+ n2 addr2) addr1)
                    (<= (+ 1 addr1) addr2))
                (canonical-address-p addr1)
                (canonical-address-p addr2)
                (implies (posp n2) (canonical-address-p (+ -1 n2 addr2))))
           (equal (memi (bvchop 48 addr1) (write n2 addr2 val x86))
                  (memi (bvchop 48 addr1) x86)))
  :hints (("Goal" :in-theory (enable memi))))

(defthm memi-of-write-irrel
  (implies (and (<= n (bvchop 48 (- addr1 addr2))) ; use bvminus?
                (integerp addr1)
                (integerp addr2)
;                (natp n)
                )
           (equal (memi addr1 (write n addr2 val x86))
                  (memi addr1 x86)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable memi separate))))

(defthm memi-of-write-same
  (implies (and (<= n (expt 2 48))
                (unsigned-byte-p 48 addr)
                (posp n)
                )
           (equal (memi addr (write n addr val x86))
                  (bvchop 8 val)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (write n addr val x86)
           :expand (write 1 addr val x86)
           :in-theory (enable write write-byte))))

(defthm memi-of-write-not-irrel
  (implies (and (< (bvchop 48 (- addr1 addr2)) n) ;rephrase?
                (integerp addr2)
                (unsigned-byte-p 48 addr1)
                (<= n (expt 2 48))
                (integerp n) ;(natp n)
                )
           (equal (memi addr1 (write n addr2 val x86))
                  (acl2::slice (+ 7 (* 8 (bvminus 48 addr1 addr2)))
                               (* 8 (bvminus 48 addr1 addr2))
                               val)))
  :hints (("Goal"
           :expand ((write n addr2 val x86)
                    (write 1 addr1 val x86)
                    (write n 0 val x86))
           :induct (write n addr2 val x86)
           :in-theory (e/d (write bvplus acl2::bvchop-of-sum-cases app-view bvuminus bvminus write-byte)
                           ( acl2::bvminus-becomes-bvplus-of-bvuminus)))))

(defthmd write-of-!memi-high
  (implies (and (< (+ addr2 n -1) addr)
;                (natp n)
                (natp addr2)
                (integerp addr))
           (equal (write n addr2 val2 (!memi addr val x86))
                  (!memi addr val (write n addr2 val2 x86))))
  :hints (("Subgoal *1/3" :cases ((equal n 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (WRITE N ADDR2 VAL2 X86)
           :in-theory (enable write !memi
                              ACL2::BVCHOP-PLUS-1-SPLIT
                              ACL2::BVCHOP-OF-SUM-CASES
                              write-byte)
           :expand ((:free (addr val x86) (WRITE 1 ADDR VAL X86))
                    (:free (addr val x86) (WRITE n ADDR VAL X86))))))

;; write-of-write:

;; ;for proving other rules
;; (defthmd write-becomes-mv-nth-1-of-wb-1
;;   (implies (and (app-view x86)
;;                 (x86p x86)
;;                 (canonical-address-p addr)
;;                 (implies (posp n) (canonical-address-p (+ -1 n addr)))
;;                 )
;;            (equal (write n addr val x86)
;;                   (mv-nth 1 (wb-1 n addr :w val x86))))
;;   :hints (("Goal" :in-theory (enable write))))

;; (theory-invariant (incompatible (:rewrite write-becomes-mv-nth-1-of-wb-1)
;;                                 (:rewrite mv-nth-1-of-wb-1-becomes-write)))

(local
  (defun double-write-induct (n addr val val2 x86)
    (if (zp n)
        (list n addr val val2 x86)
      (double-write-induct (+ -1 n) (+ 1 addr)
                           (logtail 8 val)
                           (logtail 8 val2)
                           x86))))

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


;rename
;; we use logext so that negative constants are nice
(defthm write-of-bvplus-normalize
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (integerp addr))
           (equal (write n (bvplus 48 k addr) val x86)
                  (write n (+ (logext 48 k) addr) val x86)))
  :hints (("Goal" :in-theory (enable write-when-bvchops-agree
                                     acl2::bvchop-of-+-becomes-bvplus))))

(defthm write-of-bvplus
  (implies (and (integerp x)
                (integerp y))
           (equal (write n (bvplus 48 x y) val x86)
                  (write n (+ x y) val x86)))
  :hints (("Goal" :in-theory (enable write-when-bvchops-agree
                                     acl2::bvchop-of-+-becomes-bvplus))))

;opposite of WRITE-OF-BVPLUS
(defthmd write-of-+-arg2
  (implies (and (integerp ad1)
                (integerp ad2))
           (equal (write n (+ ad1 ad2) val x86)
                  (write n (bvplus 48 ad1 ad2) val x86)))
  :hints (("Goal" :in-theory (e/d (write) (;READ-OF-BVPLUS-TIGHTEN ; todo loop
                                          ;ACL2::BVPLUS-COMMUTATIVE-2-SIZES-DIFFER
                                          )))))

(theory-invariant (incompatible (:rewrite write-of-+-arg2) (:rewrite write-of-bvplus)))

(defthm write-of-+-normalize
  (implies (and (syntaxp (quotep k))
                (not (signed-byte-p 48 k))
                (integerp k)
                (integerp x))
           (equal (write n (+ k x) val x86)
                  (write n (+ (logext 48 k) x) val x86)))
  :hints (("Goal" :in-theory (enable write-when-bvchops-agree
                                     acl2::bvchop-of-+-becomes-bvplus))))

(defthm write-of-bvchop-arg3
  (implies t ;(natp n)
           (equal (write n ad (bvchop (* 8 n) val) x86)
                  (write n ad val x86)))
  :hints (("Goal"
           :induct (write n ad val x86)
           :in-theory (enable acl2::logtail-of-bvchop-becomes-slice
                              acl2::bvchop-of-logtail-becomes-slice
                              write)
           :expand ((write n ad val x86)
                    (write n ad (bvchop (* 8 n) val) x86)))))

(defthm write-of-bvchop-arg3-gen
  (implies (and (<= (* 8 n) m)
                (integerp n) ; (natp n)
                (natp m))
           (equal (write n ad (bvchop m val) x86)
                  (write n ad val x86)))
  :hints (("Goal" :use ((:instance write-of-bvchop-arg3 (val val))
                        (:instance write-of-bvchop-arg3 (val (bvchop m val))))
           :in-theory (disable write-of-bvchop-arg3))))

;gen
(defthm write-of-281474976710656
  (equal (write n 281474976710656 val x86)
         (write n 0 val x86))
  :hints (("Goal" :use (:instance write-of-bvchop-48 (addr 281474976710656))
           :in-theory (disable write-of-bvchop-48))))

(defthm write-of-write-byte-within
  (implies (and ;; ad2 is in the interval [ad1,ad1+n):
            (< (bvminus 48 ad2 ad1) n)
            ;; (integerp ad1)
            ;; (integerp ad2)
            (integerp n))
           (equal (write n ad1 val (write-byte ad2 byte x86))
                  (write n ad1 val x86)))
  :hints (("Goal" :induct t
           :in-theory (enable write
                              acl2::bvchop-of-sum-cases
                              bvminus
                              ifix))))

(defthm write-of-write-byte-not-within
  (implies (and ;; ad2 is NOT in the interval [ad1,ad1+n):
            (not (< (bvminus 48 ad2 ad1) n))
            ;(integerp ad1)
            ;(integerp ad2)
            ;(natp n)
            )
           (equal (write n ad1 val (write-byte ad2 byte x86))
                  (write-byte ad2 byte (write n ad1 val x86))))
  :hints (("Goal" :induct t
           :in-theory (enable write
                              acl2::bvchop-of-sum-cases
                              bvminus
                              ifix))))

(defthm write-of-write-byte-not-within-bv
  (implies (and ;; ad2 is NOT in the interval [ad1,ad1+n):
             (not (bvlt 48 (bvminus 48 ad2 ad1) n))
             (unsigned-byte-p 48 n)
             ;; (integerp ad1)
             ;; (integerp ad2)
             ;; (natp n)
             )
           (equal (write n ad1 val (write-byte ad2 byte x86))
                  (write-byte ad2 byte (write n ad1 val x86))))
  :hints (("Goal" :induct t
           :in-theory (enable bvlt write
                              acl2::bvchop-of-sum-cases
                              bvminus
                              ifix))))

;; both cases
(defthm write-of-write-byte
  (implies (and ;; (integerp ad1)
                ;; (integerp ad2)
                (integerp n))
           (equal (write n ad1 val (write-byte ad2 byte x86))
                  (if (< (bvminus 48 ad2 ad1) n)
                      ;; ad2 is in the interval [ad1,ad1+n).
                      (write n ad1 val x86)
                    (write-byte ad2 byte (write n ad1 val x86))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The main read-of-write rules start here

(defthm read-byte-of-write-irrel-gen
  (implies (and (<= n (bvminus 48 addr1 addr2))
                ;; (integerp addr2)
                ;; (integerp addr1)
                )
           (equal (read-byte addr1 (write n addr2 val x86))
                  (read-byte addr1 x86)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct t
           :in-theory (e/d (read write bvplus acl2::bvchop-of-sum-cases app-view bvuminus bvminus read-byte)
                           (acl2::bvminus-becomes-bvplus-of-bvuminus
                            acl2::bvcat-of-+-high
                            ;; for speed:
                            x86isa::memi
                            acl2::bvchop-identity)))))

;; This variant uses a hyp phrased using BV functions.
;; not yet used
(defthm read-byte-of-write-irrel-bv
  (implies (and (bvle 48 n (bvminus 48 addr1 addr2))
                (unsigned-byte-p 48 n)
                ;; (integerp addr2)
                ;; (integerp addr1)
                )
           (equal (read-byte addr1 (write n addr2 val x86))
                  (read-byte addr1 x86)))
  :hints (("Goal" :in-theory (enable bvlt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthm read-of-write-same-helper
    (implies (and (<= n 281474976710656) ; 2^48
                  (integerp addr) ; drop?
                  (integerp n))
             (equal (read n addr (write n addr val x86))
                    (bvchop (* 8 n) val)))
    :hints (("Goal"
             :in-theory (e/d (read write acl2::bvchop-of-logtail-becomes-slice)
                             (memi
                              (:e expt) ; memory exhaustion
                              ))))))

; same n and same address
(defthm read-of-write-same
  (implies (and (<= n 281474976710656) ; 2^48
                ;; (integerp addr)
                (integerp n))
           (equal (read n addr (write n addr val x86))
                  (bvchop (* 8 n) val)))
  :hints (("Goal" :use (:instance read-of-write-same-helper (addr (ifix addr)))
           :in-theory (e/d (ifix) (read-of-write-same-helper)))))

;todo: improve
(defthm read-of-write-irrel
  (implies (and (or (<= (+ n2 addr2) addr1)
                    (<= (+ n1 addr1) addr2))
                (canonical-address-p addr1)
                ;;(implies (posp n1) ; with this, we had lots of implies hits in the memoization
                         (canonical-address-p (+ -1 n1 addr1))
                         ;;)
                (canonical-address-p addr2)
                ;; (implies (posp n2) ; with this, we had lots of implies hits in the memoization
                (canonical-address-p (+ -1 n2 addr2))
                         ;;)
;                (natp n1)
;                (natp n2)
                )
           (equal (read n1 addr1 (write n2 addr2 val x86))
                  (read n1 addr1 x86)))
  :hints (("subgoal *1/2" :cases ((equal n1 1))
           ;:expand (WRITE N2 ADDR2 VAL X86)
           )
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (read n1 addr1 x86)
           :in-theory (enable read write separate canonical-address-p app-view read-byte))))


;todo: improve
(defthm read-of-write-when-separate
  (implies (and (separate :r n1 addr1 :r n2 addr2) ;we always turn the r-w-x params of separate into :r
                (canonical-address-p addr1)
                (implies (posp n1) (canonical-address-p (+ -1 n1 addr1)))
                (canonical-address-p addr2)
                (implies (posp n2) (canonical-address-p (+ -1 n2 addr2)))
;                (natp n1)
;                (natp n2)
;                (x86p x86)
                )
           (equal (read n1 addr1 (write n2 addr2 val x86))
                  (read n1 addr1 x86)))
  :hints (("Goal" :use (:instance read-of-write-irrel)
           :in-theory (e/d (separate) (read-of-write-irrel)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules about "read 1 byte" of "write 1 byte"

;; subsumed by read-of-write-same
(defthm read-1-of-write-1-same
  (implies t ;(integerp addr) ; drop?  maybe have write fix this arg
           (equal (read 1 addr (write 1 addr val x86))
                  (bvchop 8 val))))

(defthm read-1-of-write-1-diff
  (implies (not (equal (bvchop 48 addr1) (bvchop 48 addr2)))
           (equal (read 1 addr1 (write 1 addr2 val x86))
                  (read 1 addr1 x86)))
  :hints (("Goal" :in-theory (enable read write))))

;drop?
(defthm read-1-of-write-1-both
  (implies (and (canonical-address-p addr)
                (canonical-address-p addr2))
           (equal (read 1 addr (write 1 addr2 val x86))
                  (if (equal addr addr2)
                      (bvchop 8 val)
                    (read 1 addr x86))))
  :hints (("Goal" :cases ((< addr addr2)
                          (< addr2 addr))
           :in-theory (e/d (read) (write-of-0)))))

;; does not require canonical-address-p, but has bvchops in the RHS
(defthm read-1-of-write-1-both-alt
  (equal (read 1 addr (write 1 addr2 val x86))
         (if (equal (bvchop 48 addr) (bvchop 48 addr2))
             (bvchop 8 val)
           (read 1 addr x86)))
  :hints (("Goal" :expand (write 1 addr2 val x86)
           :in-theory (e/d (read write) (write-of-0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: gen the 1?
(defthm read-1-of-write-irrel
  (implies (and (not (bvlt 48 (bvminus 48 addr1 addr2) n))
                ;; (integerp addr1)
                ;; (integerp addr2)
                (unsigned-byte-p 48 n))
           (equal (read 1 addr1 (write n addr2 val x86))
                  (read 1 addr1 x86)))
  :hints (("Goal" :induct (write n addr2 val x86)
           :in-theory (enable read write bvminus bvlt acl2::bvchop-of-sum-cases))))

(defthm read-1-of-write-within
  (implies (and (<= ad2 ad1) ;gen
                (< ad1 (+ n ad2))
                (unsigned-byte-p 48 ad1)
                (unsigned-byte-p 48 ad2)
                (< (+ ad2 n) (expt 2 48)) ;gen
                (posp n)
                )
           (equal (read 1 ad1 (write n ad2 val x86))
                  (slice (+ 7 (* 8 (- ad1 ad2)))
                         (* 8 (- ad1 ad2))
                         val)))
  :hints (("Subgoal *1/8" :cases ((equal ad1 ad2)))
          ("Goal"   ;:expand ((WRITE N AD1 VAL X86))
           :in-theory (e/d (read write posp read-byte write-byte)
                           (MEMI-OF-WRITE-NOT-IRREL ; todo
                            )))))

;; todo: gen the 1?
;rename -bv
; needs write-of-write-byte
(defthm read-1-of-write-within-new
  (implies (and (bvlt 48 (bvminus 48 addr1 addr2) n)
                ;; (integerp addr1)
                ;; (integerp addr2)
                (unsigned-byte-p 48 n) ; allow 2^48?
                )
           (equal (read 1 addr1 (write n addr2 val x86))
                  (slice (+ 7 (* 8 (bvminus 48 addr1 addr2)))
                         (* 8 (bvminus 48 addr1 addr2))
                         val)))
  :hints (("Goal" :induct (write n addr2 val x86)
           :in-theory (enable read write bvminus bvlt acl2::bvchop-of-sum-cases
                              acl2::bvuminus-of-+ ifix))))

;; todo: gen the 1?
; This caused problems in non-Axe lifts
(defthmd read-1-of-write-both
  (implies (and ;; (integerp addr1)
                ;; (integerp addr2)
                (unsigned-byte-p 48 n) ; could allow n=2^48, but then the bvlt below would be false
                )
           (equal (read 1 addr1 (write n addr2 val x86))
                  (if (bvlt 48 (bvminus 48 addr1 addr2) n)
                      (slice (+ 7 (* 8 (bvminus 48 addr1 addr2)))
                             (* 8 (bvminus 48 addr1 addr2))
                             val)
                    (read 1 addr1 x86))))
  :hints (("Goal" :in-theory (disable read write))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;gen! can we drop this now?
;rename
(defthmd read-1-of-write-4-same
  (implies (and (natp read-ad)
                (< read-ad (bvplus 48 4 write-ad))
                (<= write-ad read-ad)
                ;(app-view x86) ;drop
                (canonical-address-p read-ad)
                ;; (canonical-address-p write-ad)
                (canonical-address-p (+ 3 write-ad))
                (natp write-ad)
                (< write-ad 5000000000) ;fixme
                ;(X86P X86)
                )
           (equal (read 1 read-ad (write 4 write-ad val x86))
                  (let ((byte-num (- read-ad write-ad)))
                    (slice (+ 7 (* 8 byte-num))
                           (* 8 byte-num)
                           val))))
  :hints (("Goal"
           :in-theory (e/d (read ;memi
                            bvplus
                            CANONICAL-ADDRESS-P
                            SIGNED-BYTE-P
                            ;;READ-BYTE
                            write
                            acl2::bvchop-of-logtail-becomes-slice
                            )
                           ( ;read
                            write-of-write-byte
                            write !memi
                            ))
           :expand ((:free (x) (WRITE 3 (+ 1 WRITE-AD)
                                      (LOGTAIL 8 VAL) x))
                    (:free (ad val x86) (WRITE 1 ad val x86))
                    (WRITE 4 WRITE-AD VAL X86)
                    (:free (x) (WRITE 2 (+ 2 WRITE-AD)
                                      (LOGTAIL 16 VAL) x))))))

;; ;; todo: move up (not easy)
;; (defthm read-byte-of-write-irrel
;;   (implies (and (or (<= (+ n2 addr2) addr1)
;;                     (<= (+ 1 addr1) addr2))
;;                 (canonical-address-p addr1)
;;                 (canonical-address-p addr2)
;;                 (implies (posp n2)
;;                          (canonical-address-p (+ -1 n2 addr2)))
;;                 ;(natp n2)
;;                 )
;;            (equal (read-byte addr1 (write n2 addr2 val x86))
;;                   (read-byte addr1 x86)))
;;   :hints (("Goal" :use (:instance read-of-write-irrel
;;                                   (n1 1))
;;            :in-theory (e/d (read) (read-of-write-irrel write)))))

;; todo: read should go to read-byte?
;; todo: gen
;drop?
;; (defthm read-1-of-write-4
;;   (implies (and (canonical-address-p addr)
;;                 (canonical-address-p (+ 3 addr)))
;;            (equal (read 1 addr (write 4 addr val x86))
;;                   (bvchop 8 val)))
;;   :hints (("Goal" :expand (write 4 addr val x86)
;;            :in-theory (enable read write))))


(defthm read-of-write-irrel-gen
  (implies (and (<= n2 (bvminus 48 addr1 addr2)) ; use bvle instead of <= ?
                (<= n1 (bvminus 48 addr2 addr1))
                ;; (natp n1)
                ;; (natp n2)
                ;; (integerp addr2)
                ;; (integerp addr1)
                )
           (equal (read n1 addr1 (write n2 addr2 val x86))
                  (read n1 addr1 x86)))
  :hints ( ;("subgoal *1/2" :cases ((equal n1 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct t
           :in-theory (e/d (read write bvplus acl2::bvchop-of-sum-cases app-view bvuminus bvminus read-when-bvchops-agree ifix)
                           (acl2::bvminus-becomes-bvplus-of-bvuminus
                            acl2::bvcat-of-+-high
                            ;; for speed:
                            acl2::bvchop-identity)))))

;; (EQUAL 0 (BVCHOP 48 (+ 1 AD2)))

;todo: make a version for read
(defthm read-byte-of-write-within
  (implies (and (< (bvminus 48 ad1 ad2) n)
                (<= n (expt 2 48))
                (integerp n)
                ;; (integerp ad1)
                ;; (integerp ad2)
                )
           (equal (read-byte ad1 (write n ad2 val x86))
                  (slice (+ 7 (* 8 (bvminus 48 ad1 ad2)))
                         (* 8 (bvminus 48 ad1 ad2))
                         val)))
  :hints (("Goal" :induct t
           :in-theory (enable read write posp read-byte write-byte
                              bvuminus
                              bvplus
                              acl2::bvchop-of-sum-cases))))

(defthm read-byte-of-write-both
  (implies (and (<= n (expt 2 48))
                (integerp n)
                ;; (integerp ad1)
                ;; (integerp ad2)
                )
           (equal (read-byte ad1 (write n ad2 val x86))
                  (if (< (bvminus 48 ad1 ad2) n)
                      (slice (+ 7 (* 8 (bvminus 48 ad1 ad2)))
                             (* 8 (bvminus 48 ad1 ad2))
                             val)
                    (read-byte ad1 x86)))))

(defthm read-of-write-byte-irrel
  (implies (and (<= 1 (bvminus 48 addr1 addr2))
                (<= n1 (bvminus 48 addr2 addr1))
                ;(natp n1)
                ;; (integerp addr2)
                ;; (integerp addr1)
                )
           (equal (read n1 addr1 (write-byte addr2 byte x86))
                  (read n1 addr1 x86)))
  :hints ( ;("subgoal *1/2" :cases ((equal n1 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (read n1 addr1 x86)
           :in-theory (e/d (read bvplus acl2::bvchop-of-sum-cases app-view bvuminus bvminus read-byte read-when-bvchops-agree ifix)
                           (acl2::bvminus-becomes-bvplus-of-bvuminus ACL2::BVCAT-OF-+-HIGH)))))

;; mixes normal forms
(defthm read-1-of-write-byte-same
  (implies (integerp addr)
           (equal (read 1 addr (write-byte addr byte x86))
                  (bvchop 8 byte)))
  :hints (("Goal" :in-theory (enable read))))



(defthm write-of-read-same
  (equal (write n ad (read n ad x86) x86)
         x86)
  :hints (("Goal" :in-theory (enable read write ifix))))

(defthm read-of-write-1-within
  (implies (and (bvlt 48 (bvminus 48 addr2 addr1) n)
                ;; (integerp addr1)
                ;; (integerp addr2)
                (unsigned-byte-p 48 n))
           (equal (read n addr1 (write 1 addr2 val x86))
                  (putbyte n (bvminus 48 addr2 addr1) val (read n addr1 x86))))
  :hints (("Goal" :induct (read n addr1 x86)
           :do-not '(generalize eliminate-destructors)
           :expand (read n addr1 (write-byte 0 val x86))
           :in-theory (e/d (read
                            write-of-1-becomes-write-byte
                            ;bvminus
                            bvplus
                            bvuminus
                            acl2::bvchop-of-sum-cases
                            bvlt
                            acl2::expt-becomes-expt-limited
                            read-when-bvchops-agree ifix)
                           ((:e expt)
                            ;;ACL2::BVCAT-EQUAL-REWRITE
                            ACL2::BVCAT-EQUAL-REWRITE-ALT)))))

(defthm read-of-write-byte-within
  (implies (and (bvlt 48 (bvminus 48 addr2 addr1) n)
                ;; (integerp addr1)
                ;; (integerp addr2)
                (unsigned-byte-p 48 n))
           (equal (read n addr1 (write-byte addr2 val x86))
                  (putbyte n (bvminus 48 addr2 addr1) val (read n addr1 x86))))
  :hints (("Goal" :use (:instance read-of-write-1-within)
           :in-theory (e/d (write) (read-of-write-1-within)))))

(defthm read-of-write-byte-within-with-<
  (implies (and (< (bvminus 48 addr2 addr1) n)
                ;; (integerp addr1)
                ;; (integerp addr2)
                (unsigned-byte-p 48 n))
           (equal (read n addr1 (write-byte addr2 val x86))
                  (putbyte n (bvminus 48 addr2 addr1) val (read n addr1 x86))))
  :hints (("Goal" :use (:instance read-of-write-byte-within)
           :in-theory (e/d (bvlt) (read-of-write-byte-within)))))

(defthm read-of-write-byte-within-with-<-same-addr
  (implies (and ;; (integerp addr)
                (unsigned-byte-p 48 n))
           (equal (read n addr (write-byte addr val x86))
                  (putbyte n 0 val (read n addr x86))))
  :hints (("Goal" :use (:instance read-of-write-byte-within-with-< (addr2 addr) (addr1 addr))
           :in-theory (e/d () (read-of-write-byte-within-with-<)))))

(defthm read-of-write-1-irrel
  (implies (and (not (bvlt 48 (bvminus 48 addr2 addr1) n))
                ;; (integerp addr1)
                ;; (integerp addr2)
                (unsigned-byte-p 48 n)
                )
           (equal (read n addr1 (write 1 addr2 val x86))
                  (read n addr1 x86)))
  :hints (("Goal" :induct t
           :in-theory (enable read WRITE-OF-1-BECOMES-WRITE-BYTE bvlt bvminus ACL2::BVCHOP-OF-SUM-CASES ifix))))

(defthm read-of-write-1-both
  (implies (and ;; (integerp addr1)
                ;; (integerp addr2)
                (unsigned-byte-p 48 n))
           (equal (read n addr1 (write 1 addr2 val x86))
                  (if (bvlt 48 (bvminus 48 addr2 addr1) n)
                      (putbyte n (bvminus 48 addr2 addr1) val (read n addr1 x86))
                    (read n addr1 x86))))
  :hints (("Goal" :in-theory (enable bvlt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this version does the !memi last
(defund write-alt (n addr val x86)
  (declare (xargs :stobjs x86
                  :guard (and (natp n)
                              (unsigned-byte-p (* 8 n) val)
                              (integerp addr))))
  (if (zp n)
      x86
      (let ((x86 (write-alt (+ -1 n)
                            (+ 1 addr)
                            (logtail 8 val)
                            x86)))
           (!memi (bvchop 48 addr)
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
           :in-theory (enable write-alt ACL2::BVCHOP-OF-SUM-CASES))))

(defthm write-alt-of-bvchop-48
  (implies (integerp addr)
           (equal (write-alt n (bvchop 48 addr) val x86)
                  (write-alt n addr val x86)))
  :hints (("Goal" :use (:instance write-alt-when-bvchops-agree
                                  (addr2 (bvchop 48 addr))
                                  (addr addr)))))

(defthm write-alt-of-plus-1-subst-constant
  (implies (and (syntaxp (not (quotep addr)))
                (equal k (bvchop 48 addr))
                (syntaxp (quotep k))
                (integerp addr))
           (equal (write-alt n (+ 1 addr) val x86)
                  (write-alt n (bvplus 48 1 k) val x86)))
  :hints (("Goal" :in-theory (enable bvplus)
           :use (:instance write-alt-when-bvchops-agree
                           (addr (+ 1 addr))
                           (addr2 (bvplus 48 1 k))))))

(defthmd write-alt-of-!memi-irrel
  (implies (and (< n (bvchop 48 (- addr addr2))) ;no wrap around
                (integerp addr)
                (integerp addr2)
                ;; (natp n)
                )
           (equal (write-alt n addr2 val2 (!memi addr val x86))
                  (!memi addr val (write-alt n addr2 val2 x86))))
  :hints ( ;("Subgoal *1/3" :cases ((equal n 1)))
          ("subgoal *1/2"
           :use (:instance x86isa::xw-of-xw-diff
                           (x86isa::val2 (BVCHOP 8 VAL2))
                           (x86isa::addr2 (bvchop 48 addr2))
                           (x86isa::addr addr)
                           (x86isa::val val)
                           (x86isa::X86 (WRITE-ALT (+ -1 N)
                                           (+ 1 ADDR2)
                                           (LOGTAIL 8 VAL2)
                                           X86))))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (WRITE-alt N ADDR2 VAL2 X86)
           :in-theory (e/d (write-alt !memi
                            ACL2::BVCHOP-PLUS-1-SPLIT
                            ACL2::BVCHOP-OF-SUM-CASES)
                           (
                            x86isa::xw-of-xw-both
                            x86isa::xw-of-xw-diff
                            X86ISA::XW-XW-INTRA-FIELD-ARRANGE-WRITES))
           :expand ((:free (addr val x86) (WRITE 1 ADDR VAL X86))
                    (:free (addr val x86) (WRITE n ADDR VAL X86))))))

(defthmd write-alt-of-xw-memi-irrel
  (implies (and (< n (bvchop 48 (- addr addr2))) ;no wrap around
                (integerp addr)
                (integerp addr2)
                ;(natp n)
                )
           (equal (write-alt n addr2 val2 (xw :mem addr val x86))
                  (xw :mem addr val (write-alt n addr2 val2 x86))))
  :hints ( ;("Subgoal *1/3" :cases ((equal n 1)))
          ("subgoal *1/2"
           :use (:instance x86isa::xw-of-xw-diff
                           (val2 (BVCHOP 8 VAL2))
                           (addr2 (bvchop 48 addr2))
                           (x86isa::addr addr)
                           (x86isa::val val)
                           (X86 (WRITE-ALT (+ -1 N)
                                           (+ 1 ADDR2)
                                           (LOGTAIL 8 VAL2)
                                           X86))))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (WRITE-alt N ADDR2 VAL2 X86)
           :in-theory (e/d (write-alt !memi
                            ACL2::BVCHOP-PLUS-1-SPLIT
                            ACL2::BVCHOP-OF-SUM-CASES)
                           (
                            x86isa::xw-of-xw-both
                            x86isa::xw-of-xw-diff
                            X86ISA::XW-XW-INTRA-FIELD-ARRANGE-WRITES))
           :expand ((:free (addr val x86) (WRITE 1 ADDR VAL X86))
                    (:free (addr val x86) (WRITE n ADDR VAL X86))))))

(defthmd write-becomes-write-alt
  (implies (and (integerp addr)
                (unsigned-byte-p 48 n) ; allow equal?
                ;(natp n)
                ;(<= n (expt 2 48))
                )
           (equal (write n addr val x86)
                  (write-alt n addr val x86)))
  :hints (("Goal" :induct (write n addr val x86)
           :in-theory (e/d (write
                            write-alt
                            !memi
                            write-alt-of-xw-memi-irrel ;write-alt-of-!memi-irrel
                            ACL2::BVPLUS-OF-+-ARG3
                            write-byte)
                           ())
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
           :in-theory (enable write !memi
                              ACL2::BVCHOP-PLUS-1-SPLIT
                              ACL2::BVCHOP-OF-SUM-CASES
                              write-byte)
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
(defthm write-of-write-same-helper
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
                                     ACL2::BVPLUS-OF-+-ARG3
                                     write-byte
                                     !memi
                                     ifix
                                     )
                           (;X86ISA::!MEMI$INLINE
                            )))))

(defthm write-of-write-byte-huge
  (implies (and (<= (expt 2 48) n) ; every address gets written!
                (integerp n)
                (integerp addr)
                (integerp addr2))
           (equal (write n addr val1 (write-byte addr2 val2 x86))
                  (write n addr val1 x86)))
  :hints (("Goal"
           :in-theory (enable write))))

(defthm write-of-write-huge
  (implies (and (<= (expt 2 48) n) ; every address gets written!
                (integerp n)
                (integerp addr)
                (integerp addr2)
                )
           (equal (write n addr val1 (write n2 addr2 val2 x86))
                  (write n addr val1 x86)))
  :hints (("Goal" :induct  (write n2 addr2 val2 x86)
           :in-theory (enable write write-of-write-byte))))

(defthm write-of-write-same
  (implies (and (unsigned-byte-p 48 n) ; drop, using write-of-write-huge?
                )
           (equal (write n addr val1 (write n addr val2 x86))
                  (write n addr val1 x86)))
  :hints (("Goal" :use (:instance write-of-write-same-helper (addr (ifix addr)))
           :in-theory (e/d (ifix) (write-of-write-same-helper)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;remove theorems about memi once we use read-byte more?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move up
(defthm write-subst-term-arg1
  (implies (and (equal (bvchop 48 ad) (bvchop 48 free))
                (syntaxp (acl2::smaller-termp free ad))
                (integerp ad)
                (integerp free))
           (equal (write n ad val x86)
                  (write n free val x86)))
  :hints (("Goal" :use ((:instance write-of-bvchop-48 (addr ad))
                        (:instance write-of-bvchop-48 (addr free)))
           :in-theory (disable write-of-bvchop-48))))

(defthm write-subst-constant-arg1
  (implies (and (equal (bvchop 48 ad) k)
                (syntaxp (and (quotep k)
                              (not (quotep ad))))
                (integerp ad)
                (integerp free))
           (equal (write n ad val x86)
                  (write n k val x86)))
  :hints (("Goal" :use ((:instance write-of-bvchop-48 (addr ad))
                        (:instance write-of-bvchop-48 (addr k)))
           :in-theory (disable write-of-bvchop-48))))

(defthm write-of-write-combine-constants-1
  (implies (and (syntaxp (and (quotep val1)
                              (quotep val2)))
                (equal (bvchop 48 ad1) (bvplus 48 n2 ad2))
                (natp n1)
                (natp n2)
                (integerp ad1)
                (integerp ad2))
           (equal (write n1 ad1 val1 (write n2 ad2 val2 x86))
                  (write (+ n1 n2)
                         ad2
                         (bvcat (* 8 n1) val1
                                (* 8 n2) val2)
                         x86)))
  :hints (("Goal" :in-theory (enable write acl2::bvcat-of-logtail-low)
           :expand ((WRITE (+ N1 N2)
                           AD2 (BVCAT (* 8 N1) VAL1 (* 8 N2) VAL2)
                           X86)))))

;todo: gen
(defthm write-of-write-of-write-same
  (implies (and (integerp addr)
;                (integerp addr2)
                (natp n)
                ;(natp n2)
                (unsigned-byte-p 48 n) ; drop? but first change the write-of-write-same
                )
           (equal (write n addr val3 (write n2 addr2 val2 (write n addr val1 x86)))
                  (write n addr val3 (write n2 addr2 val2 x86))))
  :hints (("Goal" :expand ((write n2 addr2 val2 (write n addr val1 x86))
                           (write n2 0 val2 (write n addr val1 x86))
                           (write n2 addr2 val2 (write n 0 val1 x86))
                           (write n2 0 val2 (write n 0 val1 x86)))
           :in-theory (enable write ifix)
           :do-not '(generalize eliminate-destructors)
           :induct (write n2 addr2 val2 x86))))

;todo: gen
(defthm write-of-write-of-write-of-write-same
  (implies (and (integerp addr)
                (integerp addr2)
                (integerp addr3)
                (natp n)
                (natp n2)
                (natp n3)
                (unsigned-byte-p 48 n) ; drop? but first change the write-of-write-same
                )
           (equal (write n addr val4 (write n3 addr3 val3 (write n2 addr2 val2 (write n addr val1 x86))))
                  (write n addr val4 (write n3 addr3 val3 (write n2 addr2 val2 x86)))))
  :hints (("Goal" :use ((:instance write-of-write-of-write-same
                                   (val3 val4)
                                   (n2 n3)
                                   (addr2 addr3)
                                   (val2 val3)
                                   (val1 val4)
                                   (x86 (write n2 addr2 val2 (write n addr val1 x86))))
                        (:instance write-of-write-of-write-same
                                   (val3 val4)
                                   (n2 n3)
                                   (addr2 addr3)
                                   (val2 val3)
                                   (val1 val4)
                                   (x86 (write n2 addr2 val2 x86)))
                        (:instance write-of-write-of-write-same
                                   (val3 val4)))
           :in-theory (disable write-of-write-of-write-same write))))

;; ;; write of write, with 3 intervening writes
;; ;todo: gen
;; (defthm write-of-write-of-write-of-write-of-write-same
;;   (implies (and (integerp addr)
;;                 (integerp addr2)
;;                 (integerp addr3)
;;                 (integerp addr4)
;;                 (natp n)
;;                 (natp n2)
;;                 (natp n3)
;;                 (natp n4)
;;                 (unsigned-byte-p 48 n) ; drop? but first change the write-of-write-same
;;                 )
;;            (equal (write n addr val5 (write n4 addr4 val4 (write n3 addr3 val3 (write n2 addr2 val2 (write n addr val1 x86)))))
;;                   (write n addr val5 (write n4 addr4 val4 (write n3 addr3 val3 (write n2 addr2 val2 x86))))))
;;   :hints (("Goal" :use ((:instance write-of-write-of-write-same
;;                                    (val3 val4)
;;                                    (n2 n3)
;;                                    (addr2 addr3)
;;                                    (val2 val3)
;;                                    (val1 val4)
;;                                    (x86 (write n2 addr2 val2 (write n addr val1 x86))))
;;                         (:instance write-of-write-of-write-same
;;                                    (val3 val4)
;;                                    (n2 n3)
;;                                    (addr2 addr3)
;;                                    (val2 val3)
;;                                    (val1 val4)
;;                                    (x86 (write n2 addr2 val2 x86)))
;;                         (:instance write-of-write-of-write-same
;;                                    (val3 val4)))
;;            :in-theory (disable write-of-write-of-write-same write))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; are these used?:

;; (defun double-induct-two-addrs-two-ns (n1 n2 addr addr2 val)
;;   (if (zp n1)
;;       (list n1 n2 addr addr2 val)
;;     (double-induct-two-addrs-two-ns (+ -1 n1)
;;                                    (+ -1 n2)
;;                                    (+ 1 addr)
;;                                    (+ 1 addr2)
;;                                    (logtail 8 val))))

;; (defun double-induct-two-addrs (n addr addr2 val)
;;   (if (zp n)
;;       (list n addr addr2 val)
;;     (double-induct-two-addrs (+ -1 n)
;;                              (+ 1 addr)
;;                              (+ 1 addr2)
;;                              (logtail 8 val))))

(defthm read-of-write-within-same-address
  (implies (and (<= n1 n2)
                (<= n2 281474976710656) ; 2^48
                (integerp addr) ;drop?
                (natp n1)
                (natp n2))
           (equal (read n1 addr (write n2 addr val x86))
                  (slice (+ -1 (* 8 n1))
                         0
                         val)))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
           :expand ((READ N1 281474976710655 (WRITE (+ -1 N2) 0 (LOGTAIL 8 VAL) X86)))
           :in-theory (e/d (read
                            write
                            separate canonical-address-p app-view
                            ;read-byte write-byte
                            acl2::bvchop-of-logtail-becomes-slice
                            bvlt
                            ACL2::BVUMINUS-OF-+
                            ACL2::BVPLUS-OF-+-ARG2
                            ACL2::BVPLUS-OF-+-ARG3
                            ;bvplus
                            ;bvuminus
                            ACL2::BVCHOP-OF-SUM-CASES
                            )
                           ( ;X86ISA::!MEMI$INLINE
                            memi
                            (:e expt) ; memory exhaustion
                            )))))

;; Here we drop the inner write, because it is irrelevant, even though we don't
;; know anything about the outer write.
(defthm read-of-write-of-write-byte-irrel-inner
  (implies (and (<= 1 (bvminus 48 addr1 addr2))
                (<= n1 (bvminus 48 addr2 addr1))
                (integerp addr2)
                (integerp addr1)
                (integerp outer-addr))
           (equal (read n1 addr1 (write outer-n outer-addr outer-val (write-byte addr2 val x86)))
                  (read n1 addr1 (write outer-n outer-addr outer-val x86))))
  :hints (("Goal" :induct t :in-theory (enable write))))

;; Here we drop the inner write, because it is irrelevant, even though we don't
;; know anything about the outer write.
;; Slow proof?
(defthm read-of-write-of-write-irrel-inner
  (implies (and (<= n2 (bvminus 48 addr1 addr2))
                (<= n1 (bvminus 48 addr2 addr1))
                (<= outer-n (expt 2 48)) ; todo: if huge, the inner write is also irrel
                (integerp outer-n)
                ;(< n2 (expt 2 48))
                ;(< n1 (expt 2 48))
                ;; (natp n1)
                ;; (natp n2)
                ;; (integerp addr2)
                (integerp addr1)
                (integerp outer-addr)
                )
           (equal (read n1 addr1 (write outer-n outer-addr outer-val (write n2 addr2 val x86)))
                  (read n1 addr1 (write outer-n outer-addr outer-val x86))))
  :hints ( ;("subgoal *1/2" :cases ((equal n1 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
;           :induct (write n2 addr2 val x86)
           :induct t
           :in-theory (e/d (read
                            ;write
                            ;bvplus
                            bvuminus bvminus acl2::bvchop-of-sum-cases
                            ;app-view
                            ;read-byte
                            ifix
                            )
                           (acl2::bvminus-becomes-bvplus-of-bvuminus
                             ACL2::BVCAT-OF-+-HIGH
                             ;; for speed:
                             X86ISA::MEMI
                             acl2::BVCHOP-IDENTITY
                             )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; where should this go?
(local (include-book "kestrel/bv/bitops" :dir :system))
(defthmd part-install-width-low-of-read-becomes-bvcat-of-read
  (implies (and (natp n)
                (natp low)
                (natp width))
           (equal (bitops::part-install-width-low val (read n addr x86) width low)
                  (bvcat (- (* 8 n) (+ width low))
                         (slice (+ -1 (* 8 n)) (+ low width) (read n addr x86))
                         (+ width low)
                         (bvcat width val low (read n addr x86)))))
  :hints (("Goal" :use (:instance acl2::part-install-width-low-becomes-bvcat
                                  (x (read n addr x86))
                                  (xsize (* 8 n))
                                  (acl2::low low)
                                  (acl2::width width)
                                  (acl2::val val))
           :in-theory (disable acl2::part-install-width-low-becomes-bvcat))))

(defthm logtail-of-read-becomes-slice
  (implies (and ;(< n (* 8 n2))
                (natp n)
                (natp n2)
                )
           (equal (logtail n (read n2 addr x86))
                  (slice (+ -1 (* 8 n2)) n (read n2 addr x86))))
  :hints (("Goal" :use (:instance acl2::logtail-becomes-slice
                                  (x (read n2 addr x86))
                                  (m (* 8 n2)))
           :in-theory (disable acl2::logtail-becomes-slice))))

(defthm logapp-of-read-becomes-bvcat
  (implies (natp n2)
           (equal (logapp size i (read n2 addr x86))
                  (bvcat (* 8 n2) (read n2 addr x86) size i)))
  :hints (("Goal" :use (:instance acl2::logapp-becomes-bvcat-when-bv
                                  (jsize (* 8 n2))
                                  (j (read n2 addr x86)))
           :in-theory (e/d (unsigned-byte-p-forced) (acl2::logapp-becomes-bvcat-when-bv)))))

;move up
(defthm bvcat-of-read-and-read-combine
  (implies (and (equal (bvchop 48 ad1) (bvplus 48 n2 ad2))
                (equal size1 (* 8 n1))
                (equal size2 (* 8 n2))
                (posp n1)
                (natp n2)
                (integerp ad2)
                ;; (integerp ad1)
                )
           (equal (bvcat size1
                         (read n1 ad1 x86)
                         size2
                         (read n2 ad2 x86))
                  (read (+ n1 n2) ad2 x86)))
  :hints (("Goal" :in-theory (enable acl2::bvcat-equal-rewrite
                                     read-when-bvchops-agree
                                     acl2::bvchop-of-+-becomes-bvplus))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm riml08-becomes-read
  (implies (and (canonical-address-p lin-addr)
                (app-view x86))
           (equal (x86isa::riml08 lin-addr r-x x86)
                  (mv nil (logext 8 (read 1 lin-addr x86)) x86)))
  :hints (("Goal" :in-theory (enable x86isa::riml08))))

(defthm riml16-becomes-read
  (implies (and (canonical-address-p lin-addr)
                (canonical-address-p (+ 1 lin-addr))
                (app-view x86))
           (equal (x86isa::riml16 lin-addr r-x x86)
                  (mv nil (logext 16 (read 2 lin-addr x86)) x86)))
  :hints (("Goal" :in-theory (enable x86isa::riml16))))

(defthm riml32-becomes-read
  (implies (and (canonical-address-p lin-addr)
                (canonical-address-p (+ 3 lin-addr))
                (app-view x86))
           (equal (x86isa::riml32 lin-addr r-x x86)
                  (mv nil (logext 32 (read 4 lin-addr x86)) x86)))
  :hints (("Goal" :in-theory (enable x86isa::riml32))))

(defthm riml64-becomes-read
  (implies (and (canonical-address-p lin-addr)
                (canonical-address-p (+ 7 lin-addr))
                (app-view x86))
           (equal (x86isa::riml64 lin-addr r-x x86)
                  (mv nil (logext 64 (read 8 lin-addr x86)) x86)))
  :hints (("Goal" :in-theory (enable x86isa::riml64))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Goes directly to read.
(defthm riml-size-of-1-becomes-read
  (implies (and (canonical-address-p addr)
                (app-view x86))
           (equal (x86isa::riml-size 1 addr r-x x86)
                  (mv nil (logext 8 (read 1 addr x86)) x86))))

(defthm riml-size-of-2-becomes-read
  (implies (and (canonical-address-p addr) ; drop?
                (canonical-address-p (+ 1 addr))
                (app-view x86))
           (equal (x86isa::riml-size 2 addr r-x x86)
                  (mv nil (logext 16 (read 2 addr x86)) x86))))

(defthm riml-size-of-4-becomes-read
  (implies (and (canonical-address-p addr)
                (canonical-address-p (+ 3 addr))
                (app-view x86))
           (equal (x86isa::riml-size 4 addr r-x x86)
                  (mv nil (logext 32 (read 4 addr x86)) x86))))

(defthm riml-size-of-8-becomes-read
  (implies (and (canonical-address-p addr)
                (canonical-address-p (+ 7 addr))
                (app-view x86))
           (equal (x86isa::riml-size 8 addr r-x x86)
                  (mv nil (logext 64 (read 8 addr x86)) x86))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(local (in-theory (disable mv-nth)))

(defthm rml-size-of-1-becomes-read
  (implies (and (canonical-address-p addr)
                (app-view x86))
           (equal (x86isa::rml-size 1 addr r-x x86)
                  (mv nil (read 1 addr x86) x86)))
  :hints (("Goal" :in-theory (enable x86isa::rml-size rb-becomes-read))))

(defthm rml-size-of-2-becomes-read
  (implies (and (canonical-address-p addr)
                (canonical-address-p (+ 1 addr))
                (app-view x86))
           (equal (x86isa::rml-size 2 addr r-x x86)
                  (mv nil (read 2 addr x86) x86)))
  :hints (("Goal" :in-theory (enable x86isa::rml-size rb-becomes-read))))

(defthm rml-size-of-4-becomes-read
  (implies (and (canonical-address-p addr)
                (canonical-address-p (+ 3 addr))
                (app-view x86))
           (equal (x86isa::rml-size 4 addr r-x x86)
                  (mv nil (read 4 addr x86) x86)))
  :hints (("Goal" :in-theory (enable x86isa::rml-size rb-becomes-read))))

(defthm rml-size-of-6-becomes-read
  (implies (and (canonical-address-p addr)
                (canonical-address-p (+ 5 addr))
                (app-view x86))
           (equal (x86isa::rml-size 6 addr r-x x86)
                  (mv nil (read 6 addr x86) x86)))
  :hints (("Goal" :in-theory (enable x86isa::rml-size rb-becomes-read))))

(defthm rml-size-of-8-becomes-read
  (implies (and (canonical-address-p addr)
                (canonical-address-p (+ 7 addr))
                (app-view x86))
           (equal (x86isa::rml-size 8 addr r-x x86)
                  (mv nil (read 8 addr x86) x86)))
  :hints (("Goal" :in-theory (enable x86isa::rml-size rb-becomes-read))))

(defthm rml-size-of-10-becomes-read
  (implies (and (canonical-address-p addr)
                (canonical-address-p (+ 9 addr))
                (app-view x86))
           (equal (x86isa::rml-size 10 addr r-x x86)
                  (mv nil (read 10 addr x86) x86)))
  :hints (("Goal" :in-theory (enable x86isa::rml-size rb-becomes-read))))

(defthm rml-size-of-16-becomes-read
  (implies (and (canonical-address-p addr)
                (canonical-address-p (+ 15 addr))
                (app-view x86))
           (equal (x86isa::rml-size 16 addr r-x x86)
                  (mv nil (read 16 addr x86) x86)))
  :hints (("Goal" :in-theory (enable x86isa::rml-size rb-becomes-read))))

(defthm rml-size-of-32-becomes-read
  (implies (and (canonical-address-p addr)
                (canonical-address-p (+ 31 addr))
                (app-view x86))
           (equal (x86isa::rml-size 32 addr r-x x86)
                  (mv nil (read 32 addr x86) x86)))
  :hints (("Goal" :in-theory (enable x86isa::rml-size rb-becomes-read))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund clear (n addr x86)
  (declare (xargs :guard (and (natp n)
                              (integerp addr))
                  :stobjs x86))
  (write n addr 0 x86))

;drop hyps?
(defthm write-of-clear
  (implies (and ;(integerp ad)
                (unsigned-byte-p 48 n))
           (equal (write n ad val (clear n ad x86))
                  (write n ad val x86)))
  :hints (("Goal" :in-theory (enable clear))))

(defthm clear-of-write-of-clear
  (implies (and (integerp ad1)
                (unsigned-byte-p 48 n1)
                ;(integerp ad2)
                (unsigned-byte-p 48 n2))
           (equal (clear n1 ad1 (write n2 ad2 val (clear n1 ad1 x86)))
                  (clear n1 ad1 (write n2 ad2 val x86))))
  :hints (("Goal" :in-theory (enable clear))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move up
(defthm write-of-write-diff-bv
  (implies (and (syntaxp (acl2::smaller-termp ad2 ad1))
                (bvle 48 n2 (bvminus 48 ad1 ad2))
                (bvle 48 n1 (bvminus 48 ad2 ad1))
                ;;(natp n1)
                (unsigned-byte-p 48 n2) ;; (natp n2)
                (unsigned-byte-p 48 n1) ;; (natp n1)
                )
           (equal (write n1 ad1 val1 (write n2 ad2 val2 x86))
                  (write n2 ad2 val2 (write n1 ad1 val1 x86))))
  :hints (("Goal" :induct t
           :in-theory (enable write ;acl2::bvuminus-of-+
                                     bvlt bvplus bvuminus bvminus
                                     acl2::bvchop-of-sum-cases))))

;can loop if enabled
(defthmd acl2::bvplus-subst-arg2
  (implies (and (equal (bvchop n x) free)
                ;(syntaxp (acl2::smaller-termp free x))
                )
           (equal (bvplus n x y)
                  (bvplus n free y)))
  :hints (("Goal" :use (:instance acl2::bvplus-subst-smaller-term-arg2
                                  (x y)
                                  (y x))
           :in-theory (disable acl2::bvplus-subst-smaller-term-arg2))))

(local
  (defthmd helper
    (implies (equal (bvchop 48 ad1) (bvplus 48 ad2 n2))
             (equal (bvplus 48 ad1 (bvuminus 48 ad2))
                    (bvchop 48 n2)))))

(local
  (defthmd helper2
    (implies (equal (bvchop 48 ad1) (bvplus 48 ad2 n2))
             (equal (bvplus 48 ad2 (bvuminus 48 ad1))
                    (bvuminus 48 n2)))))

(local
  (defthm helper3
    (implies (and (<= (+ n1 n2) 281474976710656)
                  (unsigned-byte-p 48 n1)
                  (unsigned-byte-p 48 n2))
             (equal (bvlt 48 (bvuminus 48 n2) n1)
                    (if (equal 0 n2)
                        (bvlt 48 0 n1)
                      nil)))
    :hints (("Goal" :in-theory (enable bvuminus bvlt)))))

;move up
(defthm write-of-write-combine-constants-2
  (implies (and (syntaxp (and (quotep val1)
                              (quotep val2)))
                (equal (bvchop 48 ad1) (bvplus 48 n2 ad2)) ; ad1 is at the end of the write to ad2
                (unsigned-byte-p 48 n1) ;(natp n1)
                (unsigned-byte-p 48 n2) ;(natp n2)
                (<= (+ n1 n2) (expt 2 48)) ;needed?
                (integerp ad1)
                (integerp ad2))
           (equal (write n2 ad2 val2 (write n1 ad1 val1 x86))
                  (write (+ n1 n2)
                         ad2
                         (bvcat (* 8 n1) val1
                                (* 8 n2) val2)
                         x86)))
  ;; :hints (("Goal" :in-theory (e/d (;write acl2::bvcat-of-logtail-low
  ;;                              (:i write)
  ;;                              write-of-1-becomes-write-byte
  ;;                              )
  ;;                                 (
  ;;                                  acl2::bvplus-when-low-bits-are-zero))
  ;;          :induct (write n1 ad1 val1 x86) ; causes the wrong first byte to be split off
  ;;          :expand ((WRITE (+ N1 N2)
  ;;                          AD2 (BVCAT (* 8 N1) VAL1 (* 8 N2) VAL2)
  ;;                          X86))))
  :hints (("Goal" :use (write-of-write-combine-constants-1
                         (:instance write-of-write-diff-bv))
           :in-theory (e/d (helper helper2)
                           (write-of-write-combine-constants-1
                            write-of-write-diff-bv)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; split the write after the first m bytes
(defthmd split-write
  (implies (and (<= m n)
                (natp n)
                (natp m)
                (natp n)
                (<= n (expt 2 48))
;                (< n (expt 2 48))
;                (unsigned-byte-p 48 n)
                (integerp ad))
           (equal (write n ad val x86)
                  (write m ad (bvchop (* 8 m) val) (write (- n m) (+ m ad) (slice (+ -1 (* 8 n)) (* 8 m) val) x86))))
  :hints (("Goal" :in-theory (enable write))))

(local
  (defthm cancel-helper
    (iff (< (+ (- (* 8 m1)) (* 8 n)) (* 8 m2))
         (< (+ (- m1) n) m2))))

;; splits the write at the first m1 bytes, the next m2 bytes, and the remaining bytes
(defthmd split-write-3
  (implies (and (<= (+ m1 m2) n)
                (natp n)
                (natp m1)
                (natp m2)
                ;;(unsigned-byte-p 48 n)
                (natp n)
                ;(<= n (expt 2 48))
                (< n (expt 2 48))
                (integerp ad))
           (equal (write n ad val x86)
                  (write m1 ad (bvchop (* 8 m1) val)
                         (write m2 (+ m1 ad) (slice (+ -1 (* 8 (+ m1 m2))) (* 8 m1) val)
                                (write (+ n (- m1) (- m2)) (+ m1 m2 ad) (slice (+ -1 (* 8 n)) (* 8 (+ m1 m2)) val) x86)))))
  :hints (("Goal" :use ((:instance split-write (m m1))
                        (:instance split-write
                                   (n (+ (- m1) n))
                                   (ad (+ ad m1))
                                   (val (slice (+ -1 (* 8 n))
                                               (* 8 m1)
                                               val))
                                   (m m2))
                        ;; (:instance write-of-bvchop-arg3-gen
                        ;;            (m (* 8 n))
                        ;;            (n m2)
                        ;;            (ad (+ ad m1))
                        ;;            (val (slice (+ -1 (* 8 n)) (* 8 m1) val))
                        ;;            (x86 (write (+ (- m1) (- m2) n)
                        ;;                        (+ ad m1 m2)
                        ;;                        (slice (+ -1 (* 8 n))
                        ;;                               (+ (* 8 m1) (* 8 m2))
                        ;;                               val)
                        ;;                        x86)))
                        )
           :cases ((zp n))
           :in-theory (e/d () (write-of-bvchop-arg3-gen
                               write-of-bvchop-arg3 ; todo: just keep the gen one?
                               )))))

;move
(defthm read-of-write-irrel-bv
  (implies (and (bvle 48 n2 (bvminus 48 addr1 addr2))
                (bvle 48 n1 (bvminus 48 addr2 addr1))
                (unsigned-byte-p 48 n1)
                (unsigned-byte-p 48 n2))
           (equal (read n1 addr1 (write n2 addr2 val x86))
                  (read n1 addr1 x86)))
  :hints (("Goal" :use (:instance read-of-write-irrel-gen)
           :in-theory (e/d (bvlt) (read-of-write-irrel-gen)))))

;; (defthm read-of-write-irrel-better
;;   (implies (and (or (<= (+ n2 (bvchop 48 addr2)) (bvchop 48 addr1))
;;                     (<= (+ n1 (bvchop 48 addr1)) (bvchop 48 addr2)))
;;                 ..
;;                 )
;;            (equal (read n1 addr1 (write n2 addr2 val x86))
;;                   (read n1 addr1 x86)))
;;   :hints (("subgoal *1/2" :cases ((equal n1 1))
;;            ;:expand (WRITE N2 ADDR2 VAL X86)
;;            )
;;           ("Goal" :do-not '(generalize eliminate-destructors)
;;            :induct (read n1 addr1 x86)
;;            :in-theory (enable read write separate canonical-address-p app-view read-byte))))

;addr1+n1 - addr2 <= n2
;move up?
;; maybe prove by first expressing the read as just a slice of the read of the entire write.
(local
  (defthm read-of-write-within-helper
    (implies (and (bvlt 48 (bvminus 48 ad1 ad2) n2) ; the start of the read is within the write
                  (<= n1 n2) ; ensures the difference is not negative
                  ;(< (bvminus 48 (bvplus 48 -1 (bvplus 48 n1 ad1)) ad2) n2)
                  ;                (<= (+ n1 (bvminus 48 ad1 ad2)) n2) ; the end of the read is within the write
                  ;(bvlt 48 (bvplus 48 -1 (bvplus 48 n1 (bvminus 48 ad1 ad2))) n2)
                  (bvle 48 (bvminus 48 ad1 ad2) (bvminus 48 n2 n1))
                  ;(<= n2 281474976710655) ; 2^48-1
                  ;(<= n1 281474976710655) ; 2^48-1
                  ;(unsigned-byte-p 48 n2) ; drop
                  (natp n2)
                  ;(<= n2 (expt 2 48))
                  (< n2 (expt 2 48))
                  (unsigned-byte-p 48 n1) ; drop
                  (unsigned-byte-p 48 ad1) ; dropped below
                  (unsigned-byte-p 48 ad2) ; dropped below
                  )
             (equal (read n1 ad1 (write n2 ad2 val x86))
                    (slice (+ -1 (* 8 (+ n1 (bvminus 48 ad1 ad2))))
                           (* 8 (bvminus 48 ad1 ad2))
                           val)))
    :hints (("Goal" :in-theory (e/d (acl2::bvminus-becomes-bvplus-of-bvuminus
                                     bvlt bvplus bvminus bvuminus acl2::bvchop-of-sum-cases
                                     )
                                    (acl2::logcar-logcdr-elim ; disable !
                                     ))
;           :expand (:with unsigned-byte-p (unsigned-byte-p 48 n2)) ; todo: uses acl2::unsigned-byte-p* !
;           :expand (unsigned-byte-p 48 n2) ; todo: uses acl2::unsigned-byte-p* !
             :cases ((bvlt '48 (bvplus '48 ad2 (bvuminus '48 ad1)) n1))
             :use (:instance split-write-3
                             (n n2)
                             (ad ad2)
                             (m1 (bvminus 48 ad1 ad2))
                             (m2 n1)
                             (val val))))))

;; or we could use subregion48p for the hyp...
(defthm read-of-write-within
  (implies (and (<= n1 n2) ; quick, necessary check.  also ensures the difference is not negative. ; todo: require strictly greater, for speed?
                (bvlt 48 (bvminus 48 ad1 ad2) n2) ; the start of the read is within the write
                (bvle 48 (bvminus 48 ad1 ad2) (bvminus 48 n2 n1)) ; the end of the read is within the write (see subregion48p)
                (unsigned-byte-p 48 n2) ; allow 2^48?
                (integerp n1)
                (integerp ad1)
                (integerp ad2))
           (equal (read n1 ad1 (write n2 ad2 val x86))
                  (slice (+ -1 (* 8 (+ n1 (bvminus 48 ad1 ad2))))
                         (* 8 (bvminus 48 ad1 ad2))
                         val)))
  :hints (("Goal" :use (:instance read-of-write-within-helper
                                  (ad1 (bvchop 48 ad1))
                                  (ad2 (bvchop 48 ad2)))
           :expand (:with unsigned-byte-p (unsigned-byte-p 48 n1))
           :in-theory (disable read-of-write-within-helper))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Read a list of chunks
;; See also read-bytes.
;; TODO: Move to own file?
(defund read-chunks (addr count bytes-per-chunk x86)
  (declare (xargs :guard (and (unsigned-byte-p 48 addr)
                              (natp count)
                              (natp bytes-per-chunk))
                  :stobjs x86))
  (if (zp count)
      nil
    (cons (read bytes-per-chunk addr x86)
          (read-chunks (bvplus 48 bytes-per-chunk addr) (+ -1 count) bytes-per-chunk x86))))

(defopeners read-chunks)
