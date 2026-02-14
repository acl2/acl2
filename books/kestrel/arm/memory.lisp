; ARM32 memory operations
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

;; STATUS: In-progress / incomplete

;; Reference: ARM Architecture Reference Manual ARMv7-A and ARMv7-R edition,
;; available from https://developer.arm.com/documentation/ddi0406/latest/

;; TODO: Deal with address wrap-around, alignment issues, and endianness issues.

(include-book "memory32")
(include-book "state")
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bvminus-def" :dir :system)
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read-chunk-little" :dir :system)
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/logtail" :dir :system))
(local (include-book "kestrel/bv/bvuminus" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/bv/convert-to-bv-rules" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system)) ; for bvchop-plus-1-split
(local (include-book "kestrel/bv/rules3" :dir :system)) ; reduce?

;todo: build in to tool
(defthm subregion32p-of-+-of--1-same
  (implies (posp n)
           (subregion32p (+ -1 n) 1 n 0))
  :hints (("Goal" :in-theory (enable subregion32p in-region32p bvlt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund addressp (ad)
  (declare (xargs :guard t))
  (unsigned-byte-p 32 ad))

(defthm addressp-forward-to-integerp
  (implies (addressp ad)
           (integerp ad))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable addressp))))

(defthm addressp-forward-to-unsigned-byte-p
  (implies (addressp ad)
           (unsigned-byte-p 32 ad))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable addressp))))

;; Every register's value can be used as an address.
(defthm addressp-of-reg
  (implies (and (< n 16)
                (natp n)
                (armp arm))
           (addressp (reg n arm)))
  :hints (("Goal" :in-theory (enable addressp))))

(defthm addressp-of-bvplus-32
  (addressp (bvplus 32 x y))
  :hints (("Goal" :in-theory (enable addressp))))

;strong
(defthm addressp-when-unsigned-byte-p-32
  (implies (unsigned-byte-p 32 a)
           (addressp a))
  :hints (("Goal" :in-theory (enable addressp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: use this more
(defund add-to-address (offset address)
  (declare (xargs :guard (and (unsigned-byte-p 32 offset)
                              (addressp address))))
  (bvplus 32 offset address))

(defthm addressp-of-add-to-address
  (addressp (add-to-address offset address))
  :hints (("Goal" :in-theory (enable add-to-address))))

(defthm unsigned-byte-p-of-add-to-address
  (unsigned-byte-p 32 (add-to-address offset address))
  :hints (("Goal" :in-theory (enable add-to-address))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: This stuff is in the ARM package, whereas for risc-v it is in the R
;; package (which corresponds to the A package for ARM)

;; Reads the byte at address ADDR.
(defund read-byte (addr arm)
  (declare (xargs :guard (unsigned-byte-p 32 addr)
                  :stobjs arm))
  (bvchop 8 (ifix (memoryi (bvchop 32 addr) arm))))

(defthm read-byte-when-not-integerp
  (implies (not (integerp addr))
           (equal (read-byte addr arm)
                  (read-byte 0 arm)))
  :hints (("Goal" :in-theory (enable read-byte))))

; maybe drop the arg1 from the name
(defthm read-byte-of-bvchop-arg1
  (equal (read-byte (bvchop 32 addr) arm)
         (read-byte addr arm))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm read-byte-of-constant-arg2
  (implies (and (syntaxp (quotep addr))
                (not (unsigned-byte-p 32 addr)))
           (equal (read-byte addr arm)
                  (read-byte (bvchop 32 addr) arm)))
  :hints (("Goal" :in-theory (enable read-byte))))

;rename to have 8 in the name?
(defthmd unsigned-byte-p-of-read-byte-simple
  (unsigned-byte-p 8 (read-byte addr arm))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm unsigned-byte-p-of-read-byte
  (implies (<= 8 size)
           (equal (unsigned-byte-p size (read-byte addr arm))
                  (natp size)))
  :hints (("Goal" :use unsigned-byte-p-of-read-byte-simple
           :cases ((integerp size))
           :in-theory (disable unsigned-byte-p-of-read-byte-simple))))

(defthm <=-of-read-byte-linear
  (<= (read-byte addr arm) 255)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable read-byte))))

(defthmd read-byte-of-+
  (implies (and (integerp x)
                (integerp y))
           (equal (read-byte (+ x y) arm)
                  (read-byte (bvplus 32 x y) arm)))
  :hints (("Goal" :in-theory (e/d (read-byte bvplus)
                                  (acl2::bvplus-of-+-arg3
                                   ;disjoint-regions32p-of-+-arg4
                                   ;in-region32p-of-+-arg3
                                   )))))

(defthmd equal-of-read-byte-and-read-byte-when-bvchops-agree
  (implies (equal (bvchop 32 addr)
                  (bvchop 32 addr2))
           (equal (equal (read-byte addr arm)
                         (read-byte addr2 arm))
                  t))
  :hints (("Goal" :in-theory (enable read-byte))))

;or do we want to introduce bvchop?
(defthm read-byte-of-+-of-bvchop-arg1
  (implies (and (integerp x)
                (integerp y))
           (equal (read-byte (+ x (bvchop 32 y)) arm)
                  (read-byte (+ x y) arm)))
  :hints (("Goal" :use ((:instance read-byte-of-bvchop-arg1 (addr (+ x (bvchop 32 y))))
                        (:instance read-byte-of-bvchop-arg1 (addr (+ x y))))
           :in-theory (disable read-byte-of-bvchop-arg1))))

;or do we want to introduce bvchop?
(defthm read-byte-of-+-of-bvchop-arg2
  (implies (and (integerp x)
                (integerp y))
           (equal (read-byte (+ (bvchop 32 y) x) arm)
                  (read-byte (+ y x) arm)))
  :hints (("Goal" :use ((:instance read-byte-of-bvchop-arg1 (addr (+ (bvchop 32 y) x)))
                        (:instance read-byte-of-bvchop-arg1 (addr (+ x y))))
           :in-theory (disable read-byte-of-bvchop-arg1))))

;or do we want to introduce bvchop?
(defthm read-byte-of-+-of-bvchop-arg2+
  (implies (and (integerp x)
                (integerp y))
           (equal (read-byte (+ x (bvchop 32 y) z) arm)
                  (read-byte (+ x y z) arm)))
  :hints (("Goal" :use ((:instance read-byte-of-bvchop-arg1 (addr (+ x (bvchop 32 y) z)))
                        (:instance read-byte-of-bvchop-arg1 (addr (+ x y z))))
           :in-theory (disable read-byte-of-bvchop-arg1))))

;dup!
(defthm bvchop-of-+-of-bvimunus-arg3
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
            (equal (bvchop 32 (+ x y (bvuminus 32 z)))
                   (bvchop 32 (+ x y (- z)))))
  :hints (("Goal" :in-theory (enable bvuminus))))

;or do we want to introduce bvchop?
(defthm read-byte-of-+-of-bvuminus-arg3
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (read-byte (+ x y (bvuminus 32 z)) arm)
                  (read-byte (+ y x (- z)) arm)))
  :hints (("Goal" :use ((:instance read-byte-of-bvchop-arg1 (addr (+ x y (bvuminus 32 z))))
                        (:instance read-byte-of-bvchop-arg1 (addr (+ y x (- z)))))
           :in-theory (e/d (;bvuminus
                            )
                           (read-byte-of-bvchop-arg1)))))

(defthm read-byte-of-+-subst-constant-arg1
  (implies (and (equal (bvchop 32 x) freek)
                (syntaxp (and (quotep freek)
                              ;; avoid loops:
                              (not (quotep x))))
                (integerp x)
                (integerp y))
           (equal (read-byte (+ x y) arm)
                  (read-byte (+ freek y) arm)))
  :hints (("Goal" :in-theory (enable read-byte-of-+))))

(defthm read-byte-of-+-subst-constant-arg2
  (implies (and (equal (bvchop 32 y) freek)
                (syntaxp (and (quotep freek)
                              (not (quotep y))))
                (integerp x)
                (integerp y))
           (equal (read-byte (+ x y) arm)
                  (read-byte (+ x freek) arm)))
  :hints (("Goal" :in-theory (enable read-byte-of-+))))

;; (local
;;   (implies (and (memoryp mem)
;;                 (natp addr)
;;                 (< addr (len mem)))
;;            (integerp (nth addr mem))))

;; (defthm unsigned-byte-p-8-of-read-byte
;;   (unsigned-byte-p 8 (read-byte addr arm))
;;   :hints (("Goal" :in-theory (enable read-byte))))

;move up
(defthm integerp-of-read-byte-type
  (integerp (read-byte addr arm))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read-byte))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Read N bytes, starting at ADDR.  Unlike read, this returns a list.
;; TODO: Consider putting the N parameter first
(defund read-bytes (n addr arm)
  (declare (xargs :guard (and (natp n)
                              (unsigned-byte-p 32 addr))
                  :stobjs arm))
  (if (zp n)
      nil
    (cons (read-byte addr arm)
          (read-bytes (+ -1 n) (bvplus 32 1 addr) arm))))

(defthm len-of-read-bytes
  (equal (len (read-bytes n addr arm))
         (nfix n))
  :hints (("Goal" :in-theory (enable read-bytes))))

(defthm car-of-read-bytes
  (implies (and (posp n)
                (integerp addr))
           (equal (car (read-bytes n addr x86))
                  (read-byte addr x86)))
  :hints (("Goal" :expand (read-bytes n addr x86))))

(local
 (defun inc-dec-dec-induct (x y z)
   (if (zp y)
       (list x y z)
     (inc-dec-dec-induct (bvplus 32 1 x) (+ -1 y) (+ -1 z)))))

(defthm nth-of-read-bytes
  (implies (and (< n1 n2)
                (natp n1)
                (natp n2)
                (integerp addr))
           (equal (nth n1 (read-bytes n2 addr x86))
                  (read-byte (bvplus 32 addr n1) x86)))
  :hints (("Goal" :induct (inc-dec-dec-induct addr n1 n2)
           :expand (read-bytes n2 addr x86)
           :in-theory (enable read-bytes
                              acl2::bvplus-of-+-arg3))))

;; todo: just use inc-dec-dec-induct
(local
  (defun dec-dec-inc-induct (n1 ad1 ad2)
    (if (zp n1)
        (list n1 ad1 ad2)
      (dec-dec-inc-induct (+ -1 n1)
                          (+ -1 ad1)
                          (+ 1 ad2)))))

;; prove from nth-of-read-bytes?
(defthm bv-array-read-of-read-bytes-helper
  (implies (and (< index len) ;(force (< index len))
                (natp index)
                (natp len)
                (integerp ad))
           (equal (bv-array-read 8 len index (read-bytes len ad arm))
                  (read-byte (bvplus 32 index ad) arm)))
  :hints (("Goal" :induct (dec-dec-inc-induct len index ad) ; (read-bytes len ad arm)
           :expand (read-bytes len ad arm)
           ;(read-induct-two-sizes len index ad arm)
           :in-theory (enable read-bytes read-byte-of-+
                              acl2::bvplus-of-+-arg2
                              acl2::bvplus-of-+-arg3))))

;;  ; todo: different from the version for x86
;; (defthm bv-array-read-of-read-bytes
;;   (implies (and (natp index)
;;                 (natp len)
;;                 (integerp ad))
;;            (equal (bv-array-read 8 len index (read-bytes len ad arm))
;;                   (if (< index len)
;;                       (read-byte (bvplus 32 index ad) arm)
;;                     0)))
;;   :hints (("Goal" :use (:instance bv-array-read-of-read-bytes-helper)
;;            :in-theory (disable bv-array-read-of-read-bytes-helper))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reads an N-byte chunk starting at ADDR (in little-endian fashion).
;; Unlike read-bytes, this returns the value as a bit-vector.
(defund read (n addr arm)
  (declare (xargs :guard (and (natp n)
                              (unsigned-byte-p 32 addr))
                  :stobjs arm))
  (if (zp n)
      0
    (let ((addr (mbe :logic (ifix addr) :exec addr)) ; treats non-integer address as 0
          )
      (bvcat (* 8 (- n 1))
             (read (- n 1) (bvplus 32 1 addr) arm)
             8
             (read-byte addr arm)))))

(defthmd read-opener
  (implies (and (syntaxp (quotep n))
                (< 1 n) ; prevents loops with read-byte-becomes-read
                (integerp n)
                )
           (equal (read n addr arm)
                  (let ((addr (ifix addr)))
                    (bvcat (* 8 (- n 1))
                           (read (- n 1) (bvplus 32 1 addr) arm)
                           8
                           (read 1 addr arm)))))
  :hints (("Goal" :expand ((read n addr arm)
                           (read 1 addr arm)
                           (read 1 0 arm)))))

;; todo: take off 4 bytes at a a time
(defthmd read-opener-to-4
  (implies (and (syntaxp (quotep n))
                (< 4 n) ; prevents loops with read-byte-becomes-read ; todo: gen the 4
                (integerp n)
                )
           (equal (read n addr arm)
                  (let ((addr (ifix addr)))
                    (bvcat (* 8 (- n 1))
                           (read (- n 1) (bvplus 32 1 addr) arm)
                           8
                           (read 1 addr arm)))))
  :hints (("Goal" :expand ((read n addr arm)
                           (read 1 addr arm)
                           (read 1 0 arm)))))


;; includes the n=0 case
(defthm read-when-not-posp-cheap
  (implies (not (posp n))
           (equal (read n addr arm)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable read))))

;; (defthm unsigned-byte-p-of-read
;;   (implies (<= (* n 8) size)
;;            (equal (unsigned-byte-p size (read n addr arm))
;;                   (natp size)))
;;   :hints (("Goal" :in-theory (enable read))))

(defthmd integerp-of-read (integerp (read n addr arm)))
(defthmd natp-of-read (natp (read n addr arm)))

(defthmd read-of-if-arg2
  (equal (read n (if test addr1 addr2) arm)
         (if test (read n addr1 arm) (read n addr2 arm))))

(defthmd read-of-if-arg3
  (equal (read n addr (if test x y))
         (if test (read n addr x) (read n addr y))))

(defthm read-when-not-integerp
  (implies (not (integerp addr))
           (equal (read n addr arm)
                  (read n 0 arm)))
  :hints (("Goal" :in-theory (enable read))))

(defthm unsigned-byte-p-of-read-simple
  (implies (natp n)
           (unsigned-byte-p (* n 8) (read n addr arm)))
  :hints (("Goal" :in-theory (enable read))))

(defthm unsigned-byte-p-of-read
  (implies (<= (* n 8) size)
           (equal (unsigned-byte-p size (read n addr arm))
                  (natp size)))
  :hints (("Goal" :in-theory (enable read))))

(defthm not-equal-of-constant-and-read
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p (* n 8) k))
                (natp n))
           (not (equal k (read n addr arm))))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-read (size (* n 8)))
           :in-theory (disable unsigned-byte-p-of-read))))

(defthmd not-equal-of-read-and-constant
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p (* n 8) k))
                (natp n))
           (not (equal (read n addr arm) k))))

(defthm <-of-read
  (implies (and (syntaxp (quotep k))
                (<= (expt 2 (* 8 n)) k)
                (natp n)
                (integerp k))
           (< (read n addr arm) k))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-read (size (* n 8)))
                  :in-theory (disable unsigned-byte-p-of-read))))



(defthmd read-of-+
  (implies (and (integerp x)
                (integerp y))
           (equal (read n (+ x y) arm)
                  (read n (bvplus 32 x y) arm)))
  :hints (("Goal" :in-theory (enable read read-byte-of-+
                                     acl2::bvplus-of-+-arg2
                                     acl2::bvplus-of-+-arg3))))

(defthmd read-becomes-read-byte
  (equal (read 1 addr arm)
         (read-byte addr arm))
  :hints (("Goal" :in-theory (enable read))))

(defthmd read-byte-becomes-read
  (equal (read-byte addr arm)
         (read 1 addr arm))
  :hints (("Goal" :in-theory (enable read))))

(local
  (defun bvchop-of-read-induct (numbits numbytes addr)
    (if (zp numbytes)
        (list numbits numbytes addr)
      (bvchop-of-read-induct (+ -8 numbits) (+ -1 numbytes) (+ 1 (ifix addr))))))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

(defthm bvchop-of-read
  (implies (and (equal 0 (mod numbits 8))
                (natp numbits)
                (natp numbytes))
           (equal (bvchop numbits (read numbytes addr arm))
                  (if (< numbits (* 8 numbytes))
                      (read (/ numbits 8) addr arm)
                    (read numbytes addr arm))))
  :hints (("Goal" :induct (bvchop-of-read-induct numbits numbytes addr)
           :expand (read numbytes addr arm)
           :in-theory (enable READ read-of-+))))

;rename since used for a read proof as well
;add -alt to name?
(local
  (defun double-write-induct-two-addrs (n addr addr2 val)
    (if (zp n)
        (list n addr addr2 val)
      (double-write-induct-two-addrs (+ -1 n)
                                     (+ 1 addr)
                                     (+ 1 addr2)
                                     (logtail 8 val)))))

(local
  (defthmd equal-of-read-and-read-when-bvchops-agree-helper
    (implies (and (equal (bvchop 32 addr)
                         (bvchop 32 addr2))
                  (integerp addr)
                  (integerp addr2))
             (equal (equal (read n addr arm)
                           (read n addr2 arm))
                    t))
    :hints (("Goal" :induct (double-write-induct-two-addrs n addr addr2 val)
             :in-theory (enable read
                                acl2::bvchop-of-sum-cases
                                equal-of-read-byte-and-read-byte-when-bvchops-agree
                                ;bvplus
                                )))))

(defthmd equal-of-read-and-read-when-bvchops-agree
  (implies (equal (bvchop 32 addr)
                  (bvchop 32 addr2))
           (equal (equal (read n addr arm)
                         (read n addr2 arm))
                  t))
  :hints (("Goal" :in-theory (enable ifix)
           :use (:instance equal-of-read-and-read-when-bvchops-agree-helper
                           (addr (ifix addr))
                           (addr2 (ifix addr2))))))

(defthm read-of-bvchop-32
  (equal (read n (bvchop 32 addr) arm)
         (read n addr arm))
  :hints (("Goal" :in-theory (enable equal-of-read-and-read-when-bvchops-agree))))

(defthm read-of-+-bvchop-arg2
  (implies (and (integerp k)
                (integerp ad))
           (equal (read n (+ k (bvchop 32 ad)) arm)
                  (read n (+ k ad) arm)))
  :hints (("Goal" :use ((:instance read-of-bvchop-32 (addr (+ k (bvchop 32 ad))))
                        (:instance read-of-bvchop-32 (addr (+ k ad))))
           :in-theory (disable read-of-bvchop-32
                               ;acl2::bvchop-sum-drop-bvchop-alt
                               ))))

(defthm read-of-+-subst-arg2
  (implies (and (equal (bvchop 32 ad) free)
                (syntaxp (smaller-termp free ad))
                (integerp k)
                (integerp ad))
           (equal (read n (+ k ad) arm)
                  (read n (+ k free) arm))))

(defthm read-normalize-constant-arg2
  (implies (and (syntaxp (quotep addr))
                (not (unsigned-byte-p 32 addr)))
           (equal (read n addr arm)
                  (read n (bvchop 32 addr) arm))))

(local (include-book "kestrel/bv/arith" :dir :system)) ; todo, for acl2::integerp-squeeze

(local
  (defun read-high-low-induct (n addr high low)
    (if (zp n)
        (mv n addr high low)
      (read-high-low-induct (- n 1) (+ 1 addr) (+ -8 high) (+ -8 low)))))

;for whole bytes
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
           (equal (slice high low (read n addr arm))
                  (read (/ (+ 1 high (- low)) 8) ; number of bytes to read
                        (+ (/ low 8) ; number of bytes we skip
                           addr)
                        arm)))
  :hints (("subgoal *1/2" :cases ((< high 7)))
          ("Goal" :induct (read-high-low-induct n addr high low)
           :do-not '(generalize eliminate-destructors)
           :expand ((read n addr arm)
                    (read (+ 1/8 (* 1/8 high)) addr arm))
           :in-theory (e/d (read acl2::integerp-squeeze read-of-+)
                           (acl2::<=-of-*-and-*-same-linear
                            acl2::<=-of-*-and-*-same-alt-linear
                            ;; these seemed to add stuff to the goal itself?!  why?
                            acl2::<-of-*-and-*-same-forward-1
                            acl2::<-of-*-and-*-same-forward-2
                            acl2::<-of-*-and-*-same-forward-3
                            acl2::<-of-*-and-*-same-forward-4)))))



(local (include-book "kestrel/arithmetic-light/limit-expt" :dir :system))

(local
  (defthmd bvplus-helper
    (implies (and (< x n2)
                  (unsigned-byte-p 32 n2) ; gen?
                  (unsigned-byte-p 32 x) ; if we keep this, simplify the rhs
                  ;(integerp x)
                  (natp n2))
             (equal (< (bvplus 32 1 x) n2)
                    (not (and ;(unsigned-byte-p 32 n2)
                           (equal (bvchop 32 x) (bvminus 32 n2 1))
                           (not (equal (bvchop 32 x) (+ -1 (expt 2 32))))))))
    :hints (("Goal" :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases)
                                    (acl2::bvplus-of-+-arg3
                                     disjoint-regions32p-of-+-arg4
                                     in-region32p-of-+-arg3))))))

(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

;(include-book "kestrel/bv-lists/bv-array-conversions" :dir :system)
(include-book "kestrel/bv-lists/bv-list-read-chunk-little" :dir :system)

(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

;; The next rules get information from hyps of the for (equal (read-bytes ...) XXX).
;; The XXX may be a constant list of bytes (e.g., from a section/segment of the executable)
;; We might also have an append or a repeat if there are zeros?  Perhaps just split off the trailing zeros of a segment.
;; Or it might be a term that introduces variables for the bytes (a cons nest)

;; Which variant of the rule do we want?
;; Assume we have a constant list of bytes.  Then if the index into this list
;; (cyclic difference between ad1 and ad2) is a constant, we can use either
;; form and expect the read to resolve to a constant.  If the index is not a
;; constant, we probably want the variant of the rule that introduces bv-array-read-chunk-little.

;; However, if the XXX is a cons nest, we probably want the variant of the rule
;; that introduces bv-list-read-chunk-little.

;; Alternatively, we could create a version of read-bytes that returns an array
;; and always use that.

;; todo: think about whether the BYTES term will be a cons nest or bv-array-write nest
(defthm read-when-equal-of-read-bytes-and-subregion32p
  (implies (and (equal bytes (read-bytes n2 ad2 arm)) ; lots of free vars here ; note that refine-assumptions... puts the constant first
                (syntaxp (quotep bytes))
                (subregion32p n1 ad1 n2 ad2)
                ;; (syntaxp (quotep bytes)) ; maybe uncomment
                ;; (unsigned-byte-p 32 n1)
                (natp n1)
                (< n1 (expt 2 32)) ; allow equal?
                (unsigned-byte-p 32 n2) ; allow 2^32?
                (unsigned-byte-p 32 n1) ; todo
                (integerp ad1) ; todo
                (integerp ad2) ; todo
                (unsigned-byte-p 32 ad1) ; drop?
                (unsigned-byte-p 32 ad2) ; drop?
                )
           (equal (read n1 ad1 arm)
                  (bv-array-read-chunk-little n1 8 (len bytes) (bvminus 32 ad1 ad2) bytes)
                  ;; btw, the call of list-to-bv-array on a bit array is slow..
                  ;; (acl2::bv-list-read-chunk-little 8 n1 (bvminus 32 ad1 ad2) bytes)
                  ))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
;           :expand (read n1 ad1 arm)
           :expand ((read n1 ad1 arm)
                    (bv-array-read-chunk-little n1 8 n2 ad1 (read-bytes n2 0 arm))
                    (bv-array-read-chunk-little n1 8 n2 (+ (bvchop 32 ad1) (bvuminus 32 ad2)) (read-bytes n2 ad2 arm))
                    (bv-array-read-chunk-little n1 8 n2 (bvchop 32 (+ ad1 (- ad2))) (read-bytes n2 ad2 arm))
;                    (bv-array-read-chunk-little n1 8 ad1 (list-to-bv-array 8 (read-bytes n2 0 arm)))
 ;                   (bv-array-read-chunk-little n1 8 (bvchop 32 (+ ad1 (- ad2))) (list-to-bv-array 8 (read-bytes n2 ad2 arm)))
                    )
           :induct (read n1 ad1 arm)
           :in-theory (e/d ((:i read)
                            bvplus
                            ;bvuminus
                            bvuminus
                            ;acl2::bvchop-of-sum-cases
                            subregion32p
                            bvlt
                            in-region32p
                            read-becomes-read-byte
                            ifix
                            ;read-byte-of-+
                            ;read-of-+ ; loops with bvplus
                            acl2::expt-becomes-expt-limited
                            bvplus-helper
                            zp
                            unsigned-byte-p
                            ;acl2::packbv-little
                            ;; acl2::cdr-of-nthcdr
                            ;;acl2::packbv-little-opener
                            acl2::bvchop-plus-1-split
                            )
                           (;distributivity
                            acl2::+-of-minus-constant-version ; fixme disable
                            (:e expt)
                            acl2::bvplus-of-+-arg3
                            disjoint-regions32p-of-+-arg4
                            in-region32p-of-+-arg3
                            ;bvchop-of-read ;looped, but we need it
                            ;acl2::bvcat-equal-rewrite acl2::bvcat-equal-rewrite-alt ; looped
                            ;; for speed:
                            ;acl2::usb-when-usb8
                            ;acl2::bvchop-identity
                            in-region32p-when-in-region32p-and-subregion32p
                            ;acl2::bound-lemma-for-adder
                            acl2::<-of-*-same-linear-special
                            )))))

(defthm read-when-equal-of-read-bytes-and-subregion32p-alt
  (implies (and (equal (read-bytes n2 ad2 arm) bytes) ; ad2 and n2 and bytes are free vars
                (syntaxp (quotep bytes))
                (subregion32p n1 ad1 n2 ad2)
                ;; (unsigned-byte-p 32 n1)
                (natp n1)
                (< n1 (expt 2 32)) ; allow equal?
                (unsigned-byte-p 32 n2) ; allow 2^32?
                (unsigned-byte-p 32 n1) ; todo
                (integerp ad1) ; todo
                (integerp ad2) ; todo
                (unsigned-byte-p 32 ad1) ; drop?
                (unsigned-byte-p 32 ad2) ; drop?
                )
           (equal (read n1 ad1 arm)
                  ;;(acl2::bv-list-read-chunk-little 8 n1 (bvminus 32 ad1 ad2) bytes)
                  (bv-array-read-chunk-little n1 8 (len bytes) (bvminus 32 ad1 ad2) bytes)
                  ))
  :hints (("Goal" :use read-when-equal-of-read-bytes-and-subregion32p
           :in-theory (disable read-when-equal-of-read-bytes-and-subregion32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this version treats BYTES as a list and goes to bv-list-read-chunk-little

(defthm read-when-equal-of-read-bytes
  (implies (and (equal bytes (read-bytes n2 ad2 arm)) ; lots of free vars here ; note that refine-assumptions... puts the constant first
                (subregion32p n1 ad1 n2 ad2)
                ;; (syntaxp (quotep bytes)) ; maybe uncomment
                ;; (unsigned-byte-p 32 n1)
                (natp n1)
                (< n1 (expt 2 32)) ; allow equal?
                (unsigned-byte-p 32 n2) ; allow 2^32?
                (unsigned-byte-p 32 n1) ; todo
                (integerp ad1) ; todo
                (integerp ad2) ; todo
                (unsigned-byte-p 32 ad1) ; drop?
                (unsigned-byte-p 32 ad2) ; drop?
                )
           (equal (read n1 ad1 arm)
                  (bv-list-read-chunk-little 8 n1 (bvminus 32 ad1 ad2) bytes)))
  :hints (("Goal" :induct (read n1 ad1 arm)
           :in-theory (e/d ((:i read)
                            read-bytes
                            bvplus
                            ;bvuminus
                            bvuminus
                            ;acl2::bvchop-of-sum-cases
                            subregion32p
                            bvlt
                            in-region32p
                            read-becomes-read-byte
                            ifix
                            ;read-byte-of-+
                            ;read-of-+ ; loops with bvplus
                            acl2::expt-becomes-expt-limited
                            bvplus-helper
                            zp
                            unsigned-byte-p
                            ;acl2::packbv-little
                            acl2::packbv-little-opener
                            ;; acl2::cdr-of-nthcdr
                            ;;acl2::packbv-little-opener
                            acl2::nthcdr-of-cdr-combine ; todo this name and cdr-of-nthcdr are not parallel
                            acl2::cdr-of-nthcdr
                            acl2::bvchop-plus-1-split
                            bv-list-read-chunk-little
                            )
                           (;distributivity
                            acl2::+-of-minus-constant-version ; fixme disable
                            (:e expt)
                            acl2::bvplus-of-+-arg3
                            disjoint-regions32p-of-+-arg4
                            in-region32p-of-+-arg3
                            ;bvchop-of-read ;looped, but we need it
                            ;acl2::bvcat-equal-rewrite acl2::bvcat-equal-rewrite-alt ; looped
                            ;; for speed:
                            ;;acl2::usb-when-usb8
                            ;;acl2::bvchop-identity
                            in-region32p-when-in-region32p-and-subregion32p
                            ;acl2::bound-lemma-for-adder
                            acl2::<-of-*-same-linear-special
                            )))))

;; flips the equality in hyp 1
(defthm read-when-equal-of-read-bytes-alt
  (implies (and (equal (read-bytes n2 ad2 arm) bytes) ; lots of free vars here ; note that refine-assumptions... puts the constant first
                (subregion32p n1 ad1 n2 ad2)
                ;; (syntaxp (quotep bytes)) ; maybe uncomment
                ;; (unsigned-byte-p 32 n1)
                (natp n1)
                (< n1 (expt 2 32)) ; allow equal?
                (unsigned-byte-p 32 n2) ; allow 2^32?
                (unsigned-byte-p 32 n1) ; todo
                (integerp ad1) ; todo
                (integerp ad2) ; todo
                (unsigned-byte-p 32 ad1) ; drop?
                (unsigned-byte-p 32 ad2) ; drop?
                )
           (equal (read n1 ad1 arm)
                  (bv-list-read-chunk-little 8 n1 (bvminus 32 ad1 ad2) bytes)))
  :hints (("Goal" :use read-when-equal-of-read-bytes
           :in-theory (disable read-when-equal-of-read-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun CurrentModeIsNotUser ()
  (declare (xargs :guard t))
  nil ; todo
  )

(defun CurrentModeIsHyp ()
  (declare (xargs :guard t))
  nil ; todo
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; See B2.4.4 (Aligned memory accesses)
;; (defun MemA_with_priv (address size privileged wasaligned)
;;   (declare (xargs :guard (and (addressp address)
;;                               (integerp size)
;;                               (booleanp privileged)
;;                               (booleanp wasaligned))))


;; TODO: Handle alignment and privileges
(defund MemA (address size arm)
  (declare (xargs :guard (and (addressp address)
                              (posp size) ; restrict?
                              )
                  :stobjs arm))
  (read size address arm))

;; (defun MemA (address size)
;;   (declare (xargs :guard (and (addressp address)
;;                               (integerp size))))
;;   (MemA_with_priv address size (CurrentModeIsNotUser) t))

(defthm unsigned-byte-p-of-MemA
  (implies (and (posp size)
                (<= (* 8 size) n)
                (natp n))
           (unsigned-byte-p n (MemA address size arm)))
  :hints (("Goal" :in-theory (enable MemA))))

(defthm addressp-of-MemA
  (addressp (MemA address 4 arm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See B2.4.5 (Unaligned memory accesses)

;; (defun MemU_with_priv (address size privileged)
;;   (declare (xargs :guard (and (addressp address)
;;                               (integerp size)
;;                               (booleanp privileged))))

;; TODO: Handle alignment and privileges
(defund MemU (address size arm)
  (declare (xargs :guard (and (addressp address)
                              (posp size) ; restrict?
                              )
                  :stobjs arm))
  (read size address arm))

(defthm unsigned-byte-p-of-MemU
  (implies (and (posp size)
                (<= (* 8 size) n)
                (natp n))
           (unsigned-byte-p n (MemU address size arm)))
  :hints (("Goal" :in-theory (enable MemU))))

(defthm addressp-of-MemU
  (addressp (MemU address 4 arm)))

;; TODO: Handle alignment and privileges
(defund MemU_unpriv (address size arm)
  (declare (xargs :guard (and (addressp address)
                              (posp size) ; restrict?
                              )
                  :stobjs arm))
  (read size address arm))

(defthm unsigned-byte-p-of-MemU_unpriv
  (implies (and (posp size)
                (<= (* 8 size) n)
                (natp n))
           (unsigned-byte-p n (MemU_unpriv address size arm)))
  :hints (("Goal" :in-theory (enable MemU_unpriv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Writes the BYTE at address ADDR.
(defund write-byte (addr byte arm)
  (declare (xargs :guard (and (unsigned-byte-p 32 addr)
                              (unsigned-byte-p 8 byte))
                  :stobjs arm))
  (update-memoryi (bvchop 32 addr) (bvchop 8 byte) arm))

(defthm armp-of-write-byte
  (implies (and ;(unsigned-byte-p 32 addr)
                ;(unsigned-byte-p 8 byte)
                (armp arm))
           (armp (write-byte addr byte arm)))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm reg-of-write-byte
  (equal (reg reg (write-byte addr byte arm))
         (reg reg arm))
  :hints (("Goal" :in-theory (enable write-byte reg))))

(defthm error-of-write-byte
  (equal (error (write-byte addr byte arm))
         (error arm))
  :hints (("Goal" :in-theory (enable write-byte error))))

(defthm arch-version-of-write-byte
  (equal (arch-version (write-byte addr byte arm))
         (arch-version arm))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm isetstate-of-write-byte
  (equal (isetstate (write-byte addr byte arm))
         (isetstate arm))
  :hints (("Goal" :in-theory (enable write-byte isetstate))))

(defthm update-memoryi-when-not-integerp
  (implies (not (integerp addr))
           (equal (update-memoryi addr val arm)
                  (update-memoryi 0 val arm)))
  :hints (("Goal" :in-theory (enable update-memoryi))))

(defthm write-byte-when-not-integerp
  (implies (not (integerp addr))
           (equal (write-byte addr val arm)
                  (write-byte 0 val arm)))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm write-byte-of-bvchop-32
  (equal (write-byte (bvchop 32 addr) val arm)
         (write-byte addr val arm))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthmd write-byte-of-+
  (implies (and (integerp x)
                (integerp y))
           (equal (write-byte (+ x y) val arm)
                  (write-byte (bvplus 32 x y) val arm)))
  :hints (("Goal" :in-theory (e/d (write-byte bvplus)
                                  (acl2::bvplus-of-+-arg3
                                   disjoint-regions32p-of-+-arg4
                                   in-region32p-of-+-arg3)))))

(theory-invariant (incompatible (:rewrite write-byte-of-+) (:definition bvplus)))

(defthm write-byte-of-bvchop-8
  (equal (write-byte addr (bvchop 8 val) arm)
         (write-byte addr val arm))
  :hints (("Goal" :in-theory (enable write-byte))))

;rename
(defthm write-byte-subst-term-arg1
  (implies (and (equal (bvchop 32 ad) (bvchop 32 free))
                (syntaxp (smaller-termp free ad))
                ;(integerp ad)
                ;(integerp free)
                )
           (equal (write-byte ad byte arm)
                  (write-byte free byte arm)))
  :hints (("Goal" :in-theory (enable write-byte))))

;rename
(defthm write-byte-subst-arg1
  (implies (and (equal (bvchop 32 ad) freek)
                (syntaxp (and (quotep freek)
                              (not (quotep ad))))
                (integerp ad)
                (integerp freek))
           (equal (write-byte ad byte arm)
                  (write-byte freek byte arm))))

(defthm write-byte-subst-const-arg1
  (implies (and (syntaxp (not (quotep ad)))
                (equal (bvchop 32 ad) free)
                (syntaxp (quotep free))
                ;(integerp ad)
                ;(integerp free)
                )
           (equal (write-byte ad byte arm)
                  (write-byte free byte arm)))
  :hints (("Goal" :in-theory (enable))))

(defthm write-byte-of-write-byte-same
  (equal (write-byte ad byte1 (write-byte ad byte2 arm))
         (write-byte ad byte1 arm))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm write-byte-of-write-byte-diff
  (implies (and (syntaxp (smaller-termp ad2 ad1))
                (not (equal (bvchop 32 ad1)
                            (bvchop 32 ad2))))
           (equal (write-byte ad1 byte1 (write-byte ad2 byte2 arm))
                  (write-byte ad2 byte2 (write-byte ad1 byte1 arm))))
  :hints (("Goal" :in-theory (enable write-byte bvchop))))

(defthm write-byte-of-write-byte-gen
  (implies (syntaxp (smaller-termp ad2 ad1))
           (equal (write-byte ad1 byte1 (write-byte ad2 byte2 arm))
                  (if (equal (bvchop 32 ad1)
                             (bvchop 32 ad2))
                      (write-byte ad1 byte1 arm)
                    (write-byte ad2 byte2 (write-byte ad1 byte1 arm)))))
  :hints (("Goal" :use write-byte-of-write-byte-diff
                  :in-theory (disable write-byte-of-write-byte-diff))))

;;move
(local
  (defun double-write-induct (n addr val val2)
    (if (zp n)
        (list n addr val val2)
      (double-write-induct (+ -1 n) (+ 1 addr)
                           (logtail 8 val)
                           (logtail 8 val2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules about read-byte and write-byte

;; Could weaken to just require the bvchops to be equal
(defthm read-byte-of-write-byte-same
  (equal (read-byte addr (write-byte addr byte arm))
         (bvchop 8 byte))
  :hints (("Goal" :in-theory (enable read-byte write-byte))))

(defthm read-byte-of-write-byte-diff
  (implies (not (equal (bvchop 32 addr1)
                       (bvchop 32 addr2)))
           (equal (read-byte addr1 (write-byte addr2 byte arm))
                  (read-byte addr1 arm)))
  :hints (("Goal" :in-theory (enable read-byte write-byte))))

;; Handles both cases (same address, different address).
(defthm read-byte-of-write-byte
  (equal (read-byte addr1 (write-byte addr2 byte arm))
         (if (equal (bvchop 32 addr1)
                    (bvchop 32 addr2))
             (bvchop 8 byte)
           (read-byte addr1 arm)))
  :hints (("Goal" :in-theory (enable))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Writes the N-byte chunk VAL starting at ADDR (in little endian fashion).
(defund write (n addr val arm)
  (declare (xargs :guard (and (natp n)
                              (unsigned-byte-p (* 8 n) val)
                              (unsigned-byte-p 32 addr))
                  :stobjs arm))
  (if (zp n)
      arm
    (let ((arm (write-byte addr (bvchop 8 val) arm)))
      (write (+ -1 n)
             (bvplus 32 1 addr)
             (logtail 8 val) ;(slice (+ -1 (* 8 n)) 8 val)
             arm))))

(defthm write-when-not-integerp
  (implies (not (integerp addr))
           (equal (write n addr val arm)
                  (write n 0 val arm)))
  :hints (("Goal" :in-theory (enable write))))

(local
 (defun write-sub8-induct (n addr val arm size)
   (declare (xargs :stobjs arm
                   :verify-guards nil
                   ))
   (if (zp n)
       (mv n addr val arm size)
     (let ((arm (write-byte addr (bvchop 8 val) arm)))
       (write-sub8-induct (+ -1 n)
                          (bvplus 32 1 addr)
                          (logtail 8 val) ;(slice (+ -1 (* 8 n)) 8 val)
                          arm
                          (+ -8 size))))))

(defthm write-of-bvchop-arg3
  (implies (and (<= (* 8 n) size)
                (integerp size)
                (natp n))
           (equal (write n addr (bvchop size val) arm)
                  (write n addr val arm)))
  :hints (("Goal" :expand (write n addr (bvchop size val) arm)
           :induct (write-sub8-induct n addr val arm size)
           :in-theory (enable write acl2::logtail-of-bvchop))))

(defthm write-of-logext-arg3
  (implies (and (<= (* 8 n) size)
                (integerp size)
                (natp n))
           (equal (write n addr (logext size val) arm)
                  (write n addr val arm)))
  :hints (("Goal" :use ((:instance write-of-bvchop-arg3)
                        (:instance write-of-bvchop-arg3 (val (logext size val)))))))

(defthm write-of-bvchop-32-arg2
  (equal (write n (bvchop 32 addr) val arm)
         (write n addr val arm))
  :hints (("Goal" :expand (write n (bvchop 32 addr) val arm)
           :in-theory (enable write))))

(defthmd write-of-1-becomes-write-byte
  (equal (write 1 addr val arm)
         (write-byte addr val arm))
  :hints (("Goal" :expand (write 1 addr val arm)
           :in-theory (enable write))))

;; We use WRITE as the normal form
(defthmd write-byte-becomes-write
  (equal (write-byte addr val arm)
         (write 1 addr val arm))
  :hints (("Goal" :expand (write 1 addr val arm)
           :in-theory (enable write))))

(theory-invariant (incompatible (:rewrite write-byte-becomes-write) (:rewrite write-of-1-becomes-write-byte)))

(defthm error-of-write
  (equal (error (write n addr byte arm))
         (error arm))
  :hints (("Goal" :in-theory (enable write))))

(defthm arch-version-of-write
  (equal (arch-version (write n addr byte arm))
         (arch-version arm))
  :hints (("Goal" :in-theory (enable write))))

(defthm isetstate-of-write
  (equal (isetstate (write n addr byte arm))
         (isetstate arm))
  :hints (("Goal" :in-theory (enable write))))

(defthmd write-of-+
  (implies (and (integerp x)
                (integerp y))
           (equal (write n (+ x y) val arm)
                  (write n (bvplus 32 x y) val arm)))
  :hints (("Goal" :in-theory (enable write write-byte-of-+ acl2::bvplus-of-+-arg3))))

(defthm write-of-+-bvchop-arg2
  (implies (and (integerp k)
                (integerp ad))
           (equal (write n (+ k (bvchop 32 ad)) val arm)
                  (write n (+ k ad) val arm)))
  :hints (("Goal" :use ((:instance write-of-bvchop-32-arg2 (addr (+ k (bvchop 32 ad))))
                        (:instance write-of-bvchop-32-arg2 (addr (+ k ad))))
           :in-theory (disable write-of-bvchop-32-arg2))))

(defthm write-of-+-subst-arg2
  (implies (and (equal (bvchop 32 ad) free)
                (syntaxp (smaller-termp free ad))
                (integerp k)
                (integerp ad))
           (equal (write n (+ k ad) val arm)
                  (write n (+ k free) val arm))))

(defthm write-of-4294967296
  (equal (write n 4294967296 val arm)
         (write n 0 val arm))
  :hints (("Goal" :use (:instance write-of-bvchop-32-arg2
                                  (addr 4294967296))
           :in-theory (disable write-of-bvchop-32-arg2))))

(defthm write-normalize-constant-arg2
  (implies (and (syntaxp (quotep addr))
                (not (unsigned-byte-p 32 addr)))
           (equal (write n addr val arm)
                  (write n (bvchop 32 addr) val arm))))

(defthm write-normalize-constant-arg3
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (not (unsigned-byte-p (* n 8) k))
                (natp n)
                )
           (equal (write n addr k arm)
                  (write n addr (bvchop (* n 8) k) arm))))

(defthm write-of-write-byte-within-bv
  (implies (and (bvlt 32 (bvminus 32 ad2 ad1) n) ;; ad2 is in the interval [ad1,ad1+n):
                (natp n))
           (equal (write n ad1 val (write-byte ad2 byte arm))
                  (write n ad1 val arm)))
  :hints (("Goal" :induct t
           :in-theory (enable write
                              acl2::bvchop-of-sum-cases
                              bvminus
                              ifix
                              zp
                              acl2::bvlt-convert-arg2-to-bv
                              acl2::trim-of-+-becomes-bvplus ; enable by default?
                              acl2::trim-of-unary---becomes-bvuminus ; enable by default?
                              acl2::bvplus-convert-arg3-to-bv))))

;drop?
(defthm write-of-write-byte-within
  (implies (and (< (bvminus 32 ad2 ad1) n) ;; ad2 is in the interval [ad1,ad1+n):
                (integerp n))
           (equal (write n ad1 val (write-byte ad2 byte arm))
                  (write n ad1 val arm)))
  :hints (("Goal" :induct t
           :in-theory (enable write
                              acl2::bvchop-of-sum-cases
                              bvminus
                              bvplus
                              ifix))))

(defthm write-of-write-byte-disjoint-bv
  (implies (and (not (bvlt 32 (bvminus 32 ad2 ad1) n)) ;; ad2 is NOT in the interval [ad1,ad1+n):
                (unsigned-byte-p 32 n) ;; allow 2^32?
                )
           (equal (write n ad1 val (write-byte ad2 byte arm))
                  (write-byte ad2 byte (write n ad1 val arm))))
  :hints (("Goal" :induct t
           :in-theory (enable write
                              ifix
                              zp
                              acl2::bvlt-convert-arg2-to-bv
                              acl2::bvlt-convert-arg3-to-bv
                              acl2::trim-of-+-becomes-bvplus
                              acl2::trim-of-unary---becomes-bvuminus
                              acl2::bvplus-convert-arg3-to-bv))))

(defthm write-of-write-byte-huge
  (implies (and (<= (expt 2 32) n) ; every address gets written!
                (integerp n)
                (integerp addr)
                (integerp addr2))
           (equal (write n addr val1 (write-byte addr2 val2 arm))
                  (write n addr val1 arm)))
  :hints (("Goal"
           :in-theory (enable write))))

;; both cases
(defthm write-of-write-byte
  (implies (unsigned-byte-p 32 n)
           (equal (write n ad1 val (write-byte ad2 byte arm))
                  (if (bvlt 32 (bvminus 32 ad2 ad1) n)
                      ;; ad2 is in the interval [ad1,ad1+n).
                      (write n ad1 val arm)
                    (write-byte ad2 byte (write n ad1 val arm)))))
  :hints (("Goal" :cases ((unsigned-byte-p 32 n))
           :in-theory (disable acl2::bvminus-becomes-bvplus-of-bvuminus))))


;gen the n's?
(defthm write-of-write-same-helper
  (implies (and (unsigned-byte-p 32 n)
                (integerp addr))
           (equal (write n addr val1 (write n addr val2 arm))
                  (write n addr val1 arm)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (double-write-induct n addr val1 val2)
           :expand ((:free (addr val arm) (WRITE 1 ADDR VAL ARM))
                    (:free (addr val arm) (WRITE n ADDR Val ARM)))
           :in-theory (enable write
                              write-of-+
                            ;write-of-xw-mem
                              ACL2::BVPLUS-OF-+-ARG3
                              ifix))))

(defthm write-of-write-same
  (implies (and (unsigned-byte-p 32 n) ; drop, using write-of-write-huge?
                )
           (equal (write n addr val1 (write n addr val2 arm))
                  (write n addr val1 arm)))
  :hints (("Goal" :use (:instance write-of-write-same-helper (addr (ifix addr)))
           :in-theory (e/d (ifix) (write-of-write-same-helper)))))

;move
(defthm bvlt-of-bvplus-1-when-not-bvlt
  (implies (not (bvlt 32 x y))
           (equal (bvlt 32 (bvplus 32 1 x) y)
                  (and (equal (+ -1 (expt 2 32)) (bvchop 32 x))
                       (bvlt 32 0 y)
                       )))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bvlt bvplus acl2::bvchop-of-sum-cases))))

;move
(defthmd bvlt-of-1-arg2
  (equal (bvlt 32 1 x)
         (and (not (equal 0 (bvchop 32 x)))
              (not (equal 1 (bvchop 32 x)))))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm write-of-write-diff-bv-helper
  (implies (and (syntaxp (acl2::smaller-termp ad2 ad1))
                (bvle 32 n2 (bvminus 32 ad1 ad2))
                (bvle 32 n1 (bvminus 32 ad2 ad1))
                ;;(natp n1)
                (unsigned-byte-p 32 ad2) ;; for this helper
                (unsigned-byte-p 32 n2) ;; (natp n2)
                (unsigned-byte-p 32 n1) ;; (natp n1)
                )
           (equal (write n1 ad1 val1 (write n2 ad2 val2 arm))
                  (write n2 ad2 val2 (write n1 ad1 val1 arm))))
  :hints (("subgoal *1/2" :cases ((equal n2 1)))
          ("Goal" :induct t
           :in-theory (enable write ;acl2::bvuminus-of-+
                                     ;bvlt bvplus bvuminus bvminus
                                     ;acl2::bvchop-of-sum-cases
                              acl2::bvlt-convert-arg2-to-bv
                              acl2::trim-of-+-becomes-bvplus ; enable by default?
                              acl2::trim-of-unary---becomes-bvuminus ; enable by default?
                              zp
                              write-of-1-becomes-write-byte
                              bvlt-of-1-arg2))))

(defthm write-of-write-diff-bv
  (implies (and (syntaxp (acl2::smaller-termp ad2 ad1))
                (bvle 32 n2 (bvminus 32 ad1 ad2))
                (bvle 32 n1 (bvminus 32 ad2 ad1))
                (unsigned-byte-p 32 n2) ;; (natp n2)
                (unsigned-byte-p 32 n1) ;; (natp n1)
                )
           (equal (write n1 ad1 val1 (write n2 ad2 val2 arm))
                  (write n2 ad2 val2 (write n1 ad1 val1 arm))))
  :hints (("Goal" :use (:instance write-of-write-diff-bv-helper
                                  (ad2 (bvchop 32 ad2))))))

;todo: gen
(defthm write-of-write-of-write-same
  (implies (and (integerp addr)
;                (integerp addr2)
                (natp n)
                ;(natp n2)
                (unsigned-byte-p 32 n) ; drop? but first change the write-of-write-same
                (unsigned-byte-p 32 n2)
                )
           (equal (write n addr val3 (write n2 addr2 val2 (write n addr val1 arm)))
                  (write n addr val3 (write n2 addr2 val2 arm))))
  :hints (("Goal" :expand ((write n2 addr2 val2 (write n addr val1 arm))
                           (write n2 0 val2 (write n addr val1 arm))
                           (write n2 addr2 val2 (write n 0 val1 arm))
                           (write n2 0 val2 (write n 0 val1 arm)))
           :in-theory (enable write ifix)
           :do-not '(generalize eliminate-destructors)
           :induct (write n2 addr2 val2 arm))))

(defthm armp-of-write
  (implies (and (natp n)
                (unsigned-byte-p (* 8 n) val)
                (unsigned-byte-p 32 addr)
                (armp arm))
           (armp (write n addr val arm)))
  :hints (("Goal" :in-theory (enable write))))

(defthm reg-of-write
  (equal (reg reg (write n addr val arm))
         (reg reg arm))
  :hints (("Goal" :in-theory (enable write))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Handle alignment and privileges
(defun write_MemU_unpriv (address size val arm)
  (declare (xargs :guard (and (addressp address)
                              (posp size) ; restrict?
                              (unsigned-byte-p (* 8 size) val))
                  :stobjs arm))
  ;; for now:
  (write size address val arm))

;; TODO: Handle alignment and privileges
(defun write_MemU (address size val arm)
  (declare (xargs :guard (and (addressp address)
                              (posp size) ; restrict?
                              (unsigned-byte-p (* 8 size) val))
                  :stobjs arm))
  ;; for now:
  (write size address val arm))


;; TODO: Handle alignment and privileges
(defun write_MemA (address size val arm)
  (declare (xargs :guard (and (addressp address)
                              (posp size) ; restrict?
                              (unsigned-byte-p (* 8 size) val))
                  :stobjs arm))
  ;; for now:
  (write size address val arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-byte-of-set-reg
  (equal (read-byte addr (set-reg n val arm))
         (read-byte addr arm))
  :hints (("Goal" :in-theory (enable set-reg read-byte))))

(defthm read-of-set-reg
  (equal (read n addr (set-reg n2 val arm))
         (read n addr arm))
  :hints (("Goal" :in-theory (enable read))))

(defthm read-byte-of-set-apsr.n (equal (read-byte addr (set-apsr.n bit arm)) (read-byte addr arm)) :hints (("Goal" :in-theory (enable set-apsr.n read-byte))))
(defthm read-byte-of-set-apsr.z (equal (read-byte addr (set-apsr.z bit arm)) (read-byte addr arm)) :hints (("Goal" :in-theory (enable set-apsr.z read-byte))))
(defthm read-byte-of-set-apsr.c (equal (read-byte addr (set-apsr.c bit arm)) (read-byte addr arm)) :hints (("Goal" :in-theory (enable set-apsr.c read-byte))))
(defthm read-byte-of-set-apsr.v (equal (read-byte addr (set-apsr.v bit arm)) (read-byte addr arm)) :hints (("Goal" :in-theory (enable set-apsr.v read-byte))))
(defthm read-byte-of-set-apsr.q (equal (read-byte addr (set-apsr.q bit arm)) (read-byte addr arm)) :hints (("Goal" :in-theory (enable set-apsr.q read-byte))))

(defthm read-of-set-apsr.n (equal (read n addr (set-apsr.n bit arm)) (read n addr arm)) :hints (("Goal" :in-theory (enable read))))
(defthm read-of-set-apsr.z (equal (read n addr (set-apsr.z bit arm)) (read n addr arm)) :hints (("Goal" :in-theory (enable read))))
(defthm read-of-set-apsr.c (equal (read n addr (set-apsr.c bit arm)) (read n addr arm)) :hints (("Goal" :in-theory (enable read))))
(defthm read-of-set-apsr.v (equal (read n addr (set-apsr.v bit arm)) (read n addr arm)) :hints (("Goal" :in-theory (enable read))))
(defthm read-of-set-apsr.q (equal (read n addr (set-apsr.q bit arm)) (read n addr arm)) :hints (("Goal" :in-theory (enable read))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; rules about read/read-byte and write/write-byte

(defthm read-byte-of-write-irrel-gen
  (implies (and (<= n (bvminus 32 addr1 addr2)) ; use bvle?
                )
           (equal (read-byte addr1 (write n addr2 val arm))
                  (read-byte addr1 arm)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct t
           :in-theory (e/d (read write bvplus
                                 acl2::bvchop-of-sum-cases
                                 acl2::bvuminus bvminus
                                 ;read-byte
                                 ;read32-mem-ubyte8-becomes-read-byte
                                 )
                           (acl2::bvminus-becomes-bvplus-of-bvuminus
                            acl2::bvcat-of-+-high
                            acl2::bvchop-identity
                            acl2::bvplus-of-+-arg3
                            disjoint-regions32p-of-+-arg4
                            in-region32p-of-+-arg3
                            write-of-bvchop-32-arg2 ; why?
                            )))))

(defthm read-byte-of-write-within
  (implies (and (< (bvminus 32 ad1 ad2) n) ; use bvlt?
                (<= n (expt 2 32))
                (integerp n))
           (equal (read-byte ad1 (write n ad2 val arm))
                  (slice (+ 7 (* 8 (bvminus 32 ad1 ad2)))
                         (* 8 (bvminus 32 ad1 ad2))
                         val)))
  :hints (("Goal" :induct t
           :do-not '(preprocess)
           :in-theory (e/d (read
                            write posp
                            acl2::bvuminus
                            bvplus acl2::bvchop-of-sum-cases
                            ;read32-mem-ubyte8-becomes-read-byte ; todo: loop
                            acl2::expt-becomes-expt-limited
                            )
                           (acl2::bvplus-of-+-arg3
                            disjoint-regions32p-of-+-arg4
                            in-region32p-of-+-arg3
                            ;write32-mem-ubyte8-of-+-arg1 ; todo: loop
                            (:e expt)
                            )))))

(defthm read-byte-of-write-both
  (implies (and (<= n (expt 2 32))
                (integerp n))
           (equal (read-byte ad1 (write n ad2 val arm))
                  (if (< (bvminus 32 ad1 ad2) n) ; use bvlt?
                      (slice (+ 7 (* 8 (bvminus 32 ad1 ad2)))
                             (* 8 (bvminus 32 ad1 ad2))
                             val)
                    (read-byte ad1 arm)))))

(DEFTHM READ-BYTE-OF-WRITE-BOTH-new
  (IMPLIES (AND ;(<= N (EXPT 2 32))
             (unsigned-byte-p 32 n)
             (INTEGERP N))
           (EQUAL (READ-BYTE AD1 (WRITE N AD2 VAL ARM))
                  (IF (in-region32p ad1 n ad2)
                      (SLICE (+ 7 (* 8 (BVMINUS 32 AD1 AD2)))
                             (* 8 (BVMINUS 32 AD1 AD2))
                             VAL)
                    (READ-BYTE AD1 ARM))))
  :hints (("Goal" :in-theory (enable in-region32p bvlt))))

(defthm read-of-write-when-disjoint-regions32p
  (implies (and (disjoint-regions32p n1 ad1 n2 ad2)
                (integerp ad1)
                (integerp ad2)
                (unsigned-byte-p 32 n1)
                (unsigned-byte-p 32 n2))
           (equal (read n1 ad1 (write n2 ad2 val arm))
                  (read n1 ad1 arm)))
  :hints (("Goal" :in-theory (enable read write zp))))

(local
  (defthm read-of-write-same-helper
    (implies (and (<= n 4294967296) ; 2^32
                  (integerp addr) ; drop?
                  (integerp n))
             (equal (read n addr (write n addr val arm))
                    (bvchop (* 8 n) val)))
    :hints (("Goal"
             :in-theory (e/d (read write acl2::bvchop-of-logtail-becomes-slice)
                             ((:e expt) ; memory exhaustion
                              ))))))

; same n and same address
(defthm read-of-write-same
  (implies (and (<= n 4294967296) ; 2^32
                ;; (integerp addr)
                (integerp n))
           (equal (read n addr (write n addr val arm))
                  (bvchop (* 8 n) val)))
  :hints (("Goal" :use (:instance read-of-write-same-helper (addr (ifix addr)))
           :in-theory (e/d (ifix) (read-of-write-same-helper
                                   (:e expt))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-of-write-when-disjoint-regions32p-gen
  (implies (and (disjoint-regions32p len1 start1 len2 start2) ; free vars
                (subregion32p n1 ad1 len1 start1)
                (subregion32p n2 ad2 len2 start2)
                (integerp ad1)
                (integerp ad2)
                (integerp start1)
                (integerp start2)
                (unsigned-byte-p 32 n1)
                (unsigned-byte-p 32 n2))
           (equal (read n1 ad1 (write n2 ad2 val arm))
                  (read n1 ad1 arm)))
  :hints (("Goal" :in-theory (enable read write))))

(defthm read-of-write-when-disjoint-regions32p-gen-alt
  (implies (and (disjoint-regions32p len2 start2 len1 start1) ; todo: rename vars
                (subregion32p n1 ad1 len1 start1)
                (subregion32p n2 ad2 len2 start2)
                (integerp ad1)
                (integerp ad2)
                (integerp start1)
                (integerp start2)
                (unsigned-byte-p 32 n1)
                (unsigned-byte-p 32 n2))
           (equal (read n1 ad1 (write n2 ad2 val arm))
                  (read n1 ad1 arm)))
  :hints (("Goal" :use (:instance read-of-write-when-disjoint-regions32p-gen)
;           :in-theory '(disjoint-regions32p-symmetric)
           )))




(defthm read-of-write-byte-irrel
  (implies (and (<= 1 (bvminus 32 addr1 addr2)) ; todo: use bv or region phrasing?
                (<= n1 (bvminus 32 addr2 addr1))
                ;(natp n1)
                ;; (integerp addr2)
                ;; (integerp addr1)
                )
           (equal (read n1 addr1 (write-byte addr2 byte arm))
                  (read n1 addr1 arm)))
  :hints ( ;("subgoal *1/2" :cases ((equal n1 1)))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (read n1 addr1 arm)
           :in-theory (e/d (read bvplus acl2::bvchop-of-sum-cases  bvuminus bvminus equal-of-read-and-read-when-bvchops-agree ifix)
                           (acl2::bvminus-becomes-bvplus-of-bvuminus ACL2::BVCAT-OF-+-HIGH)))))

(include-book "kestrel/bv/putbits" :dir :system)

;; todo: use in-regionp?
(defthm read-of-write-1-within
  (implies (and (bvlt 32 (bvminus 32 addr2 addr1) n) ; the write is within the read
                (unsigned-byte-p 32 n))
           (equal (read n addr1 (write 1 addr2 val arm))
                  (putbyte n (bvminus 32 addr2 addr1) val (read n addr1 arm))))
  :hints (("Goal" :induct (read n addr1 arm)
           :do-not '(generalize eliminate-destructors)
           :expand (read n addr1 (write-byte 0 val arm))
           :in-theory (e/d (read
                            write-of-1-becomes-write-byte
                            ;bvminus
                            bvplus
                            bvuminus
                            acl2::bvchop-of-sum-cases
                            bvlt
                            acl2::expt-becomes-expt-limited
                            equal-of-read-and-read-when-bvchops-agree ifix)
                           ((:e expt)
                            ;;ACL2::BVCAT-EQUAL-REWRITE
                            ACL2::BVCAT-EQUAL-REWRITE-ALT)))))



(local (include-book "kestrel/arithmetic-light/limit-expt" :dir :system))
(local (acl2::limit-expt))

;; todo: gen the 1?
;rename -bv
; needs write-of-write-byte
(defthm read-1-of-write-within ; in x86, this is called read-1-of-write-within-new
  (implies (and (bvlt 32 (bvminus 32 addr1 addr2) n) ; todo: use in-regionp?
                (unsigned-byte-p 32 n) ; allow 2^32?
                )
           (equal (read 1 addr1 (write n addr2 val arm))
                  (slice (+ 7 (* 8 (bvminus 32 addr1 addr2)))
                         (* 8 (bvminus 32 addr1 addr2))
                         val)))
  :hints (("Goal" :induct (write n addr2 val arm)
           :in-theory (e/d (read write bvminus bvlt acl2::bvchop-of-sum-cases
                                 bvplus
                                 acl2::bvuminus-of-+
                                 bvuminus
                                 ifix
                                 in-region32p)
                           ((:e expt) ; todo
                            acl2::bvuminus-of-+ ; todo loop
                            )))))
