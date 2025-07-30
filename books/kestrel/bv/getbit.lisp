; BV Library: getbit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book defines getbit, a function to extract a single bit from a bit
;; vector.  Bits are numbered starting at 0 for the least significant bit.
;; Getbit is perhaps similar to the function bitn from books/rtl.

(include-book "getbit-def")
(local (include-book "slice"))
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/floor")) ;for FLOOR-DIVIDE-BY-same
(local (include-book "../arithmetic-light/floor2"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/plus-and-minus"))
(local (include-book "../arithmetic-light/floor-mod-expt"))
(local (include-book "../arithmetic-light/mod-and-expt"))
(local (include-book "unsigned-byte-p"))

(defthmd integerp-of-getbit
  (integerp (getbit index x)))

(defthmd natp-of-getbit
  (natp (getbit n x)))

(defthm getbit-of-0
  (equal (getbit n 0)
         0)
  :hints (("Goal" :in-theory (enable getbit))))

(defthm getbit-0-of-getbit
  (equal (getbit 0 (getbit n x))
         (getbit n x))
  :hints (("Goal" :in-theory (enable getbit slice))))

;gen the 1?
(defthm bvchop-1-of-getbit
  (equal (bvchop 1 (getbit n x))
         (getbit n x))
  :hints (("Goal" :in-theory (enable getbit slice))))

(defthm getbit-when-val-is-not-an-integer
  (implies (not (integerp val))
           (equal (getbit n val)
                  0))
  :hints (("Goal" :in-theory (enable getbit))))

;; Which do we prefer?
;rename
(defthmd bvchop-1-becomes-getbit
  (equal (bvchop 1 x)
         (getbit 0 x))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (enable getbit slice))))

(theory-invariant (incompatible (:rewrite bvchop-1-becomes-getbit) (:definition getbit)))

;; Not sure we want this enabled, at least during library development
(defthmd slice-becomes-getbit
  (equal (slice n n x)
         (getbit n x))
  :hints (("Goal" :in-theory (enable getbit))))

(theory-invariant (incompatible (:rewrite slice-becomes-getbit) (:definition getbit)))

;; In case we don't want to commit to either normal form
(defthm equal-of-getbit-0-and-bvchop-1
  (equal (equal (getbit 0 y) (bvchop 1 y))
         t)
  :hints (("Goal" :in-theory (enable getbit))))

;; In case we are not enforcing either normal form
(defthm equal-of-slice-and-getbit
  (equal (equal (slice n n x) (getbit n x))
         t)
  :hints (("Goal" :in-theory (enable slice-becomes-getbit))))

;justifies the correctness of some operations performed by Axe
(defthmd unsigned-byte-p-1-of-getbit
  (unsigned-byte-p 1 (getbit n x))
  :hints (("Goal" :in-theory (enable getbit slice))))

(defthm unsigned-byte-p-of-getbit
  (implies (posp size)
           (unsigned-byte-p size (getbit n x)))
  :hints (("Goal" :use unsigned-byte-p-1-of-getbit
           :in-theory (disable unsigned-byte-p-from-bounds))))

;gen the 1
;only needed by axe?
(defthm getbit-bound
  (not (< 1 (getbit n x)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-getbit (size 1) (n n))
           :in-theory (disable unsigned-byte-p-of-getbit))))

(in-theory (disable logtail)) ;move up?

(defthm getbit-of-bvchop
  (implies (and (< m n)
                (natp m) ;drop?
                (integerp n))
           (equal (getbit m (bvchop n x))
                  (getbit m x)))
  :hints (("Goal" :cases ((natp m))
           :in-theory (e/d (getbit slice) (logtail-of-bvchop)))))

(defthmd getbit-too-high
  (implies (unsigned-byte-p n x)
           (equal (getbit n x)
                  0))
  :hints (("Goal" :in-theory (enable getbit slice))))

(defthm getbit-too-high-cheap-2
  (implies (unsigned-byte-p n x)
           (equal (getbit n x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable getbit-too-high))))

(defthm getbit-of-bvchop-too-high
  (implies (and (<= size n)
                (integerp n)
                (natp size))
           (equal (getbit n (bvchop size x))
                  0))
  :hints (("Goal" :in-theory (enable getbit-too-high))))

(defthm getbit-identity
  (implies (unsigned-byte-p 1 x)
           (equal (getbit 0 x)
                  x))
  :hints (("Goal" :use (:instance bvchop-identity (i x)
                                  (size 1))
           :in-theory (e/d (getbit) (bvchop-identity)))))

(defthm getbit-identity-free
  (implies (and (unsigned-byte-p free x)
                (equal 1 free))
           (equal (getbit 0 x)
                  x))
  :hints (("Goal" :use getbit-identity
           :in-theory (disable getbit-identity))))

;; In case we are using bitp instead of unsigned-byte-p as the normal form.
;todo: can be expensive
(defthm getbit-of-0-when-bitp
  (implies (bitp x)
           (equal (getbit 0 x)
                  x)))

(defthm high-getbit-of-getbit-is-0
  (implies (and (<= 1 m)
                (integerp m))
           (equal (getbit m (getbit n x))
                  0))
  :hints (("Goal" :in-theory (enable getbit slice))))

(defthm slice-of-getbit-too-high
  (implies (and (<= 1 low)
                (integerp low))
           (equal (slice high low (getbit n x))
                  0))
  :hints (("Goal" :in-theory (enable getbit slice))))

;todo gen
(defthm getbit-of-slice
  (implies (and (<= n (+ high (- low)))
                (natp n)
                (natp low)
                (integerp high)
                )
           (equal (getbit n (slice high low x))
;                  (if (<= n (+ high (- low)))
                  (getbit (+ low n) x)
;                   0)
                  ))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (e/d (getbit slice)
                           (logtail-of-bvchop)))))

(defthm getbit-when-not-integerp-arg1
  (implies (not (integerp n))
           (equal (getbit n x)
                  (getbit 0 x)))
  :hints (("Goal" :in-theory (enable getbit slice))))

(defthm bvchop-of-getbit
  (equal (bvchop size (getbit n x))
         (if (posp size)
             (getbit n x)
           0)))

;; logbitp is built-in to acl2
(defthm logbitp-to-getbit-equal-1
  (equal (logbitp n x)
         (equal 1 (getbit n x)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (logtail bvchop logbitp getbit slice oddp evenp
                                    equal-of-0-and-mod)
                           (slice-becomes-bvchop)))))

(defthmd getbit-when-equal-of-constant-and-bvchop
  (implies (and (equal free (bvchop size x))
                (< n size)
                (integerp size)
                (natp n))
           (equal (getbit n x)
                  (getbit n free))))

(defthm getbit-when-equal-of-constant-and-bvchop-constant-version
  (implies (and (equal free (bvchop size x))
                (syntaxp (and (quotep free)
                              (not (quotep x)) ;prevents loops
                              (quotep n)
                              (quotep size)))
                (< n size)
                (integerp size)
                (natp n))
           (equal (getbit n x)
                  (getbit n free) ;gets computed
                  )))

(defthm getbit-of-expt
  (implies (and (< size2 size) ;other case?
                (integerp size)
                (natp size2))
           (equal (getbit size2 (expt 2 size))
                  0))
  :hints (("Goal" :in-theory (enable getbit slice))))

;can be useful when getbit-too-high is disabled..
(defthm getbit-of-slice-too-high
  (implies (and (> n (- high low))
                (<= low high) ;todo
                (integerp n)
                (integerp x)
                (natp low)
                (integerp high))
           (equal (getbit n (slice high low x))
                  0))
  :hints (("Goal" :in-theory (enable getbit-too-high))))

(defthm getbit-when-n-is-negative
  (implies (< n 0)
           (equal (getbit n x)
                  (getbit 0 x)))
  :hints (("Goal" :in-theory (enable getbit))))

;todo: open less to prove this?
(defthm getbit-of-expt-2-n
  (implies (natp n)
           (equal (getbit n (expt 2 n)) 1))
  :hints (("Goal" :in-theory (e/d (getbit slice logtail)
                                  (slice-becomes-bvchop)))))

(defthm getbit-of-logtail
  (implies (and (natp n)
                (natp m))
           (equal (getbit n (logtail m x))
                  (getbit (+ m n) x)))
  :hints (("Goal" :in-theory (enable getbit))))

(defthm getbit-of-mod-of-expt
  (implies (and (< n j) ;todo: other case
                (natp n)
                (integerp j))
           (equal (getbit n (mod i (expt 2 j)))
                  (getbit n i)))
  :hints (("Goal" :in-theory (e/d (getbit)
                                  (slice-becomes-bvchop)))))


;todo: rename?
;todo: gen
(defthm getbit-of-slice-gen
  (implies (and (natp n)
                (natp low)
                (integerp high)
                (integerp x) ;todo
                (<= low high) ;todo
                )
           (equal (getbit n (slice high low x))
                  (if (<= n (+ high (- low)))
                      (getbit (+ low n) x)
                    0)))
    :hints (("Goal" :in-theory (enable getbit-of-slice-too-high))))

(defthm getbit-of-1
  (equal (getbit n 1)
         (if (zp n)
             1
           0))
  :hints (("Goal" :in-theory (enable getbit slice))))

;; Only needed by Axe?
(defthmd bitp-of-getbit
  (bitp (getbit n x)))

;; could restrict to when the v's are identical
(defthmd getbit-leibniz
  (implies (and (equal n1 n2)
                (equal v1 v2))
           (equal (equal (getbit n1 v1) (getbit n2 v2))
                  t)))

(defthm getbit-of-1-of-+-of-*-of-2
  (implies (and (bitp bit1)
                (bitp bit2))
           (equal (getbit 1 (+ bit1 (* 2 bit2)))
                  bit2))
  :hints (("Goal" :in-theory (e/d (bitp)
                                  (bitp-becomes-unsigned-byte-p)))))

(defthm getbit-when-not-1
  (implies (not (equal 1 (getbit n x)))
           (equal (getbit n x)
                  0))
  :hints (("Goal" :use (:instance usb1-cases (x (getbit n x)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthmd getbit-when-not-0
  (implies (not (equal 0 (getbit n x)))
           (equal (getbit n x)
                  1))
  :hints (("Goal" :use (:instance usb1-cases (x (getbit n x)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;may be expensive? restrict to constant n?
(defthm equal-of-getbit-and-1-forward-to-bound
  (implies (and (equal 1 (getbit n x))
                (natp x))
           (<= (expt 2 n) x))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable getbit slice logtail expt))))

(local
 (defthm unsigned-byte-p-of-bvchop-one-more-helper
   (implies (and (equal size-1 (+ -1 size))
                 (natp x)
                 (posp size))
            (equal (unsigned-byte-p size-1 (bvchop size x))
                   (equal 0 (getbit size-1 x))))
   :hints (("Goal" :cases ((equal 0 x))
            :in-theory (enable getbit slice logtail bvchop unsigned-byte-p
                               mod-of-floor-equal-rewrite
                               expt-hack)))))

(defthmd unsigned-byte-p-of-bvchop-one-more
  (implies (equal size-1 (+ -1 size))
           (equal (unsigned-byte-p size-1 (bvchop size x))
                  (if (not (posp size))
                      (natp size-1)
                    (equal 0 (getbit size-1 x)))))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvchop-one-more-helper
                                  (x (bvchop size x)))
           :cases ((posp size))
           :in-theory (disable unsigned-byte-p-of-bvchop-one-more-helper))))

(defthm getbit-of-*-of-2
  (implies (and (natp n)
                (integerp x))
           (equal (getbit n (* 2 x))
                  (if (equal n 0)
                      0
                    (getbit (+ -1 n) x))))
  :hints (("Goal" :in-theory (enable getbit slice))))

(defthm getbit-of-*-of-2-arg2+
  (implies (and (natp n)
                (integerp x)
                (integerp y))
           (equal (getbit n (* x 2 y))
                  (if (equal n 0)
                      0
                    (getbit (+ -1 n) (* x y)))))
  :hints (("Goal" :use (:instance getbit-of-*-of-2
                                  (x (* x y)))
           :in-theory (disable getbit-of-*-of-2))))

(local
 (defun sub1-sub1-induct (n i)
   (if (zp i)
       (list n i)
     (sub1-sub1-induct (+ -1 n) (+ -1  i)))))

(defthm getbit-of-*-of-expt-arg1
  (implies (and (natp n)
                (natp i)
                (integerp x))
           (equal (getbit n (* (expt 2 i) x))
                  (if (< n i)
                      0
                    (getbit (- n i) x))))
  :hints (("Goal" :expand (EXPT 2 I)
           :induct (sub1-sub1-induct n i))))

(defthm getbit-of-*-of-expt-arg2
  (implies (and (natp n)
                (natp i)
                (integerp x))
           (equal (getbit n (* x (expt 2 i)))
                  (if (< n i)
                      0
                    (getbit (- n i) x))))
  :hints (("Goal" :use getbit-of-*-of-expt-arg1
           :in-theory (disable getbit-of-*-of-expt-arg1))))

;; ;yuck! can loop!
;; (defthmd getbit-0-of-times
;;    (implies (and (integerp x) (integerp y))
;;             (equal (getbit 0 (* x y))
;;                    (getbit 0 (* (getbit 0 x) (getbit 0 y)))))
;;    :hints (("Goal" :in-theory (enable getbit))))

;rename
(defthm getbit-0-of-times-constant
  (implies (and (syntaxp (and (quotep x)
                              (not (unsigned-byte-p 1 (unquote x)))))
                (integerp x)
                (integerp y))
           (equal (getbit 0 (* x y))
                  (getbit 0 (* (getbit 0 x) y))))
  :hints (("Goal" :use (:instance bvchop-of-*-of-bvchop (size 1))
           :in-theory
           (e/d (getbit)
                ( bvchop-of-*-of-bvchop)))))

(defthm getbit-when-slice-is-known-constant
  (implies (and (equal free (slice high low x)) ;reversed the equality
                (syntaxp (quotep free))
                (<= low n)
                (<= n high)
                (natp low)
                (integerp n)
                (integerp high))
           (equal (getbit n x)
                  (getbit (- n low) free))))

;make a rule to substitute?
(defthm getbits-same-when-bvchops-same
  (implies (and (equal (bvchop free x) (bvchop free y))
                (< n free)
                (natp free)
                (natp n)
                )
           (equal (equal (getbit n x) (getbit n y))
                  t))
  :hints (("Goal" :use ((:instance GETBIT-OF-BVCHOP (m n) (n free) (x x))
                        (:instance GETBIT-OF-BVCHOP (m n) (n free) (x y)))
           :in-theory (disable GETBIT-OF-BVCHOP))))

(defthm getbit-of-+-of--1-and-expt
 (implies (and (natp n)
               (natp i))
          (equal (getbit n (+ -1 (expt 2 i)))
                 (if (< n i)
                     1
                   0)))
 :hints (("Goal" :in-theory
          (e/d (getbit slice bvchop) ; todo: disable less
               ( bvchop-of-*-of-bvchop)))))

(defthm getbit-of-0-and-+-of-1-and-*-of-2
  (implies (integerp x)
           (equal (getbit 0 (+ 1 (* 2 x)))
                  1))
  :hints (("Goal" :in-theory (enable getbit bvchop))))

(defthmd getbit-when-slice-is-known-to-be-all-ones
  (implies (and (equal free (+ 1 (slice high low x))) ; tries to match the normal form
                (equal free (expt 2 (+ 1 high (- low))))
                (<= low n)
                (<= n high)
                (natp low)
                (integerp n)
                (integerp high))
           (equal (getbit n x)
                  1))
  :hints (("Goal" :use (:instance getbit-when-slice-is-known-constant
                                  (free (+ -1 (expt 2 (+ 1 high (- low))))))
           :in-theory (disable getbit-when-slice-is-known-constant))))

;move
(defthm not-equal-of-bvchop-when-equal-of-getbit
  (implies (and (syntaxp (quotep k))
                (equal bit (getbit n x)) ; bit is a free var
                (syntaxp (quotep bit))
                (not (equal bit (getbit n k)))
                (< n size)
                (natp n)
                (integerp size))
           (not (equal k (bvchop size x)))))

; see also equal-of-bvchop-when-equal-of-getbit-widen-polarity
(defthmd equal-of-bvchop-when-equal-of-getbit-widen
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal (getbit size x) k2)
                (syntaxp (quotep k2))
                (natp size))
           (equal (equal (bvchop size x) k)
                  (and (unsigned-byte-p size k) ;gets computed
                       (equal (bvchop (+ 1 size) x)
                              ;; gets computed
                              (+ (* k2 (expt 2 size))
                                 k)))))
  :hints (("Goal" :cases ((equal 0 (MOD (FLOOR X (EXPT 2 SIZE)) 2)))
           :in-theory (enable bvchop expt-of-+
                              getbit
                              slice
                              LOGTAIL$INLINE
                              mod-of-*-of-2-and-expt))))

(defthm getbit-0-of--
  (equal (getbit 0 (- x))
         (getbit 0 x))
  :hints (("Goal" :in-theory (enable getbit))))

(defthm getbit-of-+-of-expt-gen
  (implies (and (< n i)
                (integerp x)
                (natp n)
                (integerp i))
           (equal (getbit n (+ x (expt 2 i)))
                  (getbit n x)))
  :hints (("Goal" :in-theory (enable getbit))))

(defthm getbit-of--1
  (implies (natp n)
           (equal (getbit n -1)
                  1))
  :hints (("Goal" :in-theory (enable getbit))))

(defthm equal-of-getbit-same
  (equal (equal (getbit 0 x) x)
         (unsigned-byte-p 1 x))
  :hints (("Goal" :in-theory (enable getbit-identity))))

(defthmd mod-of-2-becomes-getbit-0
  (implies (integerp x)
           (equal (mod x 2)
                  (getbit 0 x)))
  :hints (("Goal" :in-theory (enable getbit bvchop))))

(defthm getbit-of-expt-gen
  (implies (and (natp m)
                (natp n))
           (equal (getbit m (expt 2 n))
                  (if (equal m n)
                      1
                    0)))
  :hints (("Goal" :in-theory (enable getbit slice))))

(defthm getbit-of-if-two-constants
  (implies (and (syntaxp (and (quotep n)
                              (quotep x1)
                              (quotep x2))))
           (equal (getbit n (if test x1 x2))
                  (if test (getbit n x1)
                    (getbit n x2)))))
(defthm getbit-of-ash
  (implies (and (natp c) ; left shift
                (natp n))
           (equal (getbit n (ash i c))
                  (if (<= c n)
                      (getbit (- n c) i)
                    0)))
  :hints (("Goal" :in-theory (enable getbit))))

;enable?
(defthmd getbit-when-negative-and-small
  (implies (and (< x 0)
                (<= (- (expt 2 n)) x)
                (natp n)
                (integerp x))
           (equal (getbit n x)
                  1))
  :hints (("Goal" :in-theory (enable getbit slice logtail))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd getbit-when-<
  (implies (and (< x free)
                (<= free (expt 2 n))
                ;; (natp n)
                (natp x) ;could allow some negatives?
                )
           (equal (getbit n x)
                  0))
  :hints (("Goal" :use (:instance slice-too-high-is-0 (high n) (low n))
                  :in-theory (enable getbit))))

;; restricts to constants for speed
(defthm getbit-when-<-of-constant
  (implies (and (syntaxp (quotep n))
                (< x free)
                (syntaxp (quotep free))
                (<= free (expt 2 n)) ; gets computed
                ;; (natp n)
                (natp x) ;could allow some negatives?
                )
           (equal (getbit n x)
                  0))
  :hints (("Goal" :use getbit-when-<
                  :in-theory (disable getbit-when-<))))

(defthmd getbit-when-<=
  (implies (and (<= x free)
                (< free (expt 2 n))
                ;; (natp n)
                (natp free)
                (natp x) ;could allow some negatives?
                )
           (equal (getbit n x)
                  0))
  :hints (("Goal" :use (:instance getbit-when-<-of-constant (free (+ 1 free)))
                  :in-theory (disable getbit-when-<-of-constant))))

(defthm getbit-when-<=-of-constant
  (implies (and (syntaxp (quotep n))
                (<= x free)
                (syntaxp (quotep free))
                (< free (expt 2 n)) ; gets computed
                ;; (natp n)
                (natp free)
                (natp x) ;could allow some negatives?
                )
           (equal (getbit n x)
                  0))
  :hints (("Goal" :use getbit-when-<=
                  :in-theory (disable getbit-when-<=))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; x is in the upper half of the range
(defthmd getbit-when->-of-constant-helper
  (implies (and (<= (expt 2 n) x)
                (unsigned-byte-p (+ 1 n) x)
                (natp n))
           (equal (getbit n x)
                  1))
  :hints (("Goal" :in-theory (enable getbit slice logtail floor-must-be-1 unsigned-byte-p expt-of-+))))

(defthm getbit-when->-of-constant
  (implies (and (syntaxp (quotep n))
                (< free x)
                (syntaxp (quotep free))
                (<= (+ -1 (expt 2 n)) free) ; gets computed
                (unsigned-byte-p (+ 1 n) x)
                (natp n)
                ;; (natp x) ;could allow some negatives?
                )
           (equal (getbit n x)
                  1))
  :hints (("Goal" :use (:instance getbit-when->-of-constant-helper)
           :in-theory (disable getbit-when->-of-constant-helper))))

(defthm getbit-when->=-of-constant
  (implies (and (syntaxp (quotep n))
                (<= free x)
                (syntaxp (quotep free))
                (<= (expt 2 n) free) ; gets computed
                (unsigned-byte-p (+ 1 n) x)
                (natp n)
                ;; (natp x) ;could allow some negatives?
                )
           (equal (getbit n x)
                  1))
  :hints (("Goal" :use (:instance getbit-when->-of-constant-helper)
                  :in-theory (disable getbit-when->-of-constant-helper))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;gen!
(defthmd getbit-when-<=-of-high-helper
  (implies (and (<= (- (expt 2 size) (expt 2 n)) x) ; size is a free var
                (unsigned-byte-p size x)
                (< n size)
                (natp n))
           (equal (getbit n x)
                  1))
  :hints (("Goal" :use ((:instance getbit-when-slice-is-known-to-be-all-ones
                                   (n n)
                                   (high (+ -1 size))
                                   (low n)
                                   (free (expt 2 (+ size (- n)))))
                        (:instance equal-of-slice
                                   (k (+ -1 (EXPT 2 (+ (- n)
                                                       size))))
                                   (high (+ -1 size))
                                   (low n)))
                  :in-theory (disable getbit-when-slice-is-known-to-be-all-ones
;exponents-add
                                      ))))

(defthm getbit-when-<=-of-bvchop-and-constant-high
  (implies (and (<= k (bvchop size x)) ; k is a free var
                (<= (- (expt 2 size) (expt 2 n)) k)
                (< n size)
                (natp size)
                (natp n))
           (equal (getbit n x)
                  1))
  :hints (("Goal" :use (:instance getbit-when-<=-of-high-helper
                                  (x (bvchop size x))))))

(defthm getbit-when-<-of-bvchop-and-constant-high
  (implies (and (< k (bvchop size x)) ; k is a free var
                (<= (+ -1 (- (expt 2 size) (expt 2 n))) k)
                (< n size)
                (natp size)
                (natp n))
           (equal (getbit n x)
                  1))
  :hints (("Goal" :use (:instance getbit-when-<=-of-high-helper
                                  (x (bvchop size x))))))


;; x is non-zero when any of its bits is non-zero
(defthm not-0-when-bit-not-0
  (implies (and (not (equal 0 (getbit free x)))
                (natp free))
           (not (equal 0 x))))

;; todo; prove via a rule about slice
(defthm getbit-of-floor-of-2
  (implies (and (integerp n)
                (integerp x))
           (equal (getbit n (floor x 2))
                  (if (< n 0)
                      (getbit 1 x) ; odd case
                    (getbit (+ 1 n) x))))
  :hints (("Goal" :in-theory (enable getbit slice logtail$inline expt))))
