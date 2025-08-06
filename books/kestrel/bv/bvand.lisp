; Bitwise and
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;(include-book "logand-b") ; todo
(include-book "bvchop")
(include-book "getbit")
;(include-book "ihs/basic-definitions" :dir :system) ;for logmaskp
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-mod-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "unsigned-byte-p"))
(local (include-book "logand-b"))

(defund bvand (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (logand (bvchop size x)
          (bvchop size y)))

(defthm bvand-type
  (and (integerp (bvand size x y))
       (<= 0 (bvand size x y)))
  :rule-classes :type-prescription)

(in-theory (disable (:type-prescription bvand))) ; bvand-type is at least as good

;disable?
(defthm bvand-commutative
  (equal (bvand size x y)
         (bvand size y x))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-associative
  (equal (bvand size (bvand size x y) z)
         (bvand size x (bvand size y z)))
  :hints (("Goal" :in-theory (enable bvand natp))))

(defthm bvand-commutative-2
  (equal (bvand size y (bvand size x z))
         (bvand size x (bvand size y z)))
  :hints (("Goal" :in-theory (disable bvand-associative)
           :use (bvand-associative
                 (:instance bvand-associative (x y) (y x))))))

(defthmd bvand-commute-constant
  (implies (syntaxp (and (quotep y)
                         (not (quotep x))))
           (equal (bvand size x y)
                  (bvand size y x))))

(defthm bvand-same
  (equal (bvand size x x)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-same-2
  (equal (bvand size x (bvand size x y))
         (bvand size x y))
  :hints (("Goal" :cases ((and (natp size) (integerp b) (integerp a))
                          (and (natp size) (integerp b) (not (integerp a)))
                          (and (natp size) (not (integerp b)) (integerp a))
                          (and (natp size) (not (integerp b)) (not (integerp a))))
           :in-theory (enable bvand))))

(defthm bvand-of-0-arg2
  (equal (bvand size 0 x)
         0)
  :hints (("Goal" :in-theory (enable bvand))))

;in case we don't have commutativity - drop, since we'll always commute??
(defthmd bvand-of-0-arg3
  (equal (bvand size x 0)
         0))

(defthm bvand-combine-constants
  (implies (syntaxp (and (quotep y) ;tested first to fail fast
                         (quotep x)
                         (quotep size)))
           (equal (bvand size x (bvand size y z))
                  (bvand size (bvand size x y) z))))

(defthm bvand-when-size-is-not-positive
  (implies (<= size 0)
           (equal (bvand size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-0-arg1
  (equal (bvand 0 x y)
         0))

(defthm bvand-when-x-is-not-an-integer
  (implies (not (integerp x))
           (equal (bvand size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-when-y-is-not-an-integer
  (implies (not (integerp y))
           (equal (bvand size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvand))))

(defthmd unsigned-byte-p-of-bvand-simple
  (implies (natp size)
           (unsigned-byte-p size (bvand size x y)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm unsigned-byte-p-of-bvand
  (implies (and (<= size n)
                (natp size)
                (natp n))
           (unsigned-byte-p n (bvand size x y)))
  :hints (("Goal" :use unsigned-byte-p-of-bvand-simple
           :in-theory (disable unsigned-byte-p-of-bvand-simple))))

(defthm bvchop-of-bvand
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (bvchop size1 (bvand size2 x y))
                  (bvand size1 x y)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-constant-chop-arg2
   (implies (and (syntaxp (and (quotep x)
                               (quotep size)))
                 (not (unsigned-byte-p size x))
                 (natp size) ; prevents loops
                 )
            (equal (bvand size x y)
                   (bvand size (bvchop size x) y)))
   :hints (("Goal" :in-theory (enable bvand))))

;; may not be needed if we commute constants forward
(defthm bvand-of-constant-chop-arg3
   (implies (and (syntaxp (and (quotep y)
                               (quotep size)))
                 (not (unsigned-byte-p size y))
                 (natp size) ; prevents loops
                 )
            (equal (bvand size x y)
                   (bvand size x (bvchop size y))))
   :hints (("Goal" :in-theory (enable bvand))))

;; ;improve?
;; ;drop?
;; (defthm bvand-of-bvchop-tighten
;;   (implies (and (< size1 size2)
;;                 (natp size1)
;;                 (natp size2))
;;            (equal (BVAND size1 x (BVCHOP size2 y))
;;                   (BVAND size1 x (BVCHOP size1 y))))
;;   :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-bvchop-1
  (implies (and (<= size size2)
                (integerp size2))
           (equal (bvand size (bvchop size2 x) y)
                  (bvand size x y)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-bvchop-arg1-same
  (equal (bvand size (bvchop size x) y)
         (bvand size x y))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-bvchop-2
  (implies (and (<= size size2)
                (integerp size2))
           (equal (bvand size x (bvchop size2 y))
                  (bvand size x y)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-bvchop-arg2-same
  (equal (bvand size x (bvchop size y))
         (bvand size x y))
  :hints (("Goal" :in-theory (enable bvand))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvand-with-mask-basic-arg2
  (equal (bvand size (+ -1 (expt 2 size)) x)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-with-mask-basic-arg3
  (equal (bvand size x (+ -1 (expt 2 size)))
         (bvchop size x))
  :hints (("Goal" :use bvand-with-mask-basic-arg2
           :in-theory (disable bvand-with-mask-basic-arg2))))

;lets the sizes differ
(defthm bvand-with-mask-arg2-gen
  (implies (and (natp n)
                (integerp size))
           (equal (bvand size (+ -1 (expt 2 n)) x)
                  (bvchop (min n size) x)))
  :hints (("Goal" :in-theory (enable bvand))))

;lets the sizes differ
(defthm bvand-with-mask-arg3-gen
  (implies (and (natp n)
                (integerp size))
           (equal (bvand size x (+ -1 (expt 2 n)))
                  (bvchop (min n size) x)))
  :hints (("Goal" :in-theory (enable bvand))))

;; ;; Here the mask is a constant.
;; ;requires the number of 1's in k to be size
;; (defthm bvand-with-mask
;;   (implies (and (syntaxp (quotep k)) ;new
;;                 (equal k (+ -1 (expt 2 size)))
;;                 (natp size))
;;            (equal (bvand size k x)
;;                   (bvchop size x))))

(local
 (defthmd +-of--1-and-expt2-of-integer-length-when-mask
   (implies (and (power-of-2p (+ 1 x))
                 (integerp x))
            (equal (+ -1 (expt 2 (integer-length x)))
                   x))
   :hints (("Goal" :use (:instance integer-length-of-+-of-1 (i x))
            :in-theory (enable power-of-2p)))))

;; Here the mask is a constant.
(defthm bvand-with-constant-mask-arg2
  (implies (and (syntaxp (quotep x))
                (power-of-2p (+ 1 x)) ; tests for a mask of all ones
                (integerp x)
                (natp size))
           (equal (bvand size x y)
                  (bvchop (min size (integer-length x)) y)))
  :hints (("Goal" :use (:instance bvand-with-mask-arg2-gen (x y) (n (integer-length x)))
           :in-theory (e/d (+-of--1-and-expt2-of-integer-length-when-mask)
                           (bvand-with-mask-arg2-gen
                            bvand-with-mask-arg3-gen)))))

;; In case we are not commuting constants forward
(defthmd bvand-with-constant-mask-arg3
  (implies (and (syntaxp (quotep y))
                (power-of-2p (+ 1 y)) ; tests for a mask of all ones
                (integerp y)
                (natp size))
           (equal (bvand size x y)
                  (bvchop (min size (integer-length y)) x)))
  :hints (("Goal" :use (:instance bvand-with-constant-mask-arg2 (x y) (y x))
           :in-theory (disable bvand-with-constant-mask-arg2))))

;; This one lets us completely remove the masking/chopping.  Can be useful when
;; we prefer masking to chopping but still want to eliminate masking that does
;; nothing (e.g., when generating imperative code).
(defthm bvand-with-mask-drop
  (implies (and (syntaxp (quotep x))
                (power-of-2p (+ 1 x)) ; tests for a mask of all ones
                (unsigned-byte-p (integer-length x) y) ; the masking does nothing
                (<= (integer-length x) size)
                (natp size))
           (equal (bvand size x y)
                  y))
  :hints (("Goal" :use bvand-with-constant-mask-arg2
           :in-theory (disable bvand-with-constant-mask-arg2))))

;; ;doesn't bind any free vars
;; ;add syntaxp hyp - does compute integer-length several times..
;; (defthm bvand-with-mask-better-eric
;;   (implies (and (syntaxp (quotep mask)) ;new
;;                 (logmaskp mask)
;;                 (<= (integer-length mask) size)
;;                 (natp size))
;;            (equal (bvand size mask i)
;;                   (bvchop (integer-length mask) i))))

;; ;don't need if we are commuting constants
;; (defthmd bvand-with-mask-better-eric-alt
;;   (implies (and (syntaxp (quotep mask)) ;new
;;                 (logmaskp mask)
;;                 (<= (integer-length mask) size)
;;                 (natp size))
;;            (equal (bvand size i mask)
;;                   (bvchop (integer-length mask) i)))
;;   :hints (("Goal" :use bvand-with-mask-better-eric
;;            :in-theory (disable bvand-with-mask-better-eric
;;                                bvand-with-mask-better))))

(defthm bvand-when-size-is-not-integerp
  (implies (not (integerp size))
           (equal (bvand size x y) 0))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm unsigned-byte-p-of-bvand-2
  (implies (or (unsigned-byte-p size i)
               (unsigned-byte-p size j))
           (equal (unsigned-byte-p size (bvand n i j))
                  (natp size)))
  :hints (("Goal" :cases ((<= n size))
           :in-theory (enable bvand))))

(defthm bvand-of-expt-same
  (equal (bvand size x (expt 2 size))
         0)
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-expt-same2
  (equal (bvand size (expt 2 size) x)
         0)
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bitp-of-bvand-of-1
  (bitp (bvand 1 x y))
  :rule-classes :type-prescription
  ;; :hints (("Goal" :use (:instance unsigned-byte-p-of-bvand-simple (size 1))
  ;;          :in-theory (disable unsigned-byte-p-of-bvand
  ;;                              unsigned-byte-p-of-bvand-simple)))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Introduces BVAND
(defthmd getbit-of-logand-becomes-bvand-of-getbit-and-getbit
  (equal (getbit n (logand a b))
         (bvand 1 (getbit n a)
                (getbit n b)))
  :hints (("Goal" :in-theory (enable bvand getbit-of-logand))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm getbit-of-bvand
  (implies (and (< n size)
                (natp n)
                (natp size))
           (equal (getbit n (bvand size x y))
                  (bvand 1 (getbit n x)
                           (getbit n y))))
  :hints (("Goal" :in-theory (enable bvand
                                     getbit-of-logand-becomes-bvand-of-getbit-and-getbit))))

;drop?
(defthmd getbit-of-bvand-core
  (implies (and (< n size) (posp size))
           (equal (getbit n (bvand size x y))
                  (bvand 1 (getbit n x) (getbit n y))))
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable bvand
                              getbit-of-logand-becomes-bvand-of-getbit-and-getbit))))

;bozo more like this, or a general rule with a syntaxp hyp?
(defthm getbit-of-bvand-too-high
  (implies (and (<= size n)
                (natp n)
                (natp size))
           (equal (getbit n (bvand size x y))
                  0))
  :hints (("Goal" :in-theory (enable getbit-too-high))))

(defthm getbit-of-bvand-eric
  (implies (and (< 1 size) ;if size is 0 or 1, other rules should fire?
                (< n size) ;other case?
                (natp n)
                (integerp size))
           (equal (getbit n (bvand size x y))
                  (bvand 1 (getbit n x) (getbit n y)))))

;BBOZO think more about this in the size > 1 case( ld "bvand.lisp") - do we want to push the getbit through?
;in the size=1 case (common when bit blasting) we do NOT want to push the GETBIT through - can be expensive!
(defthm getbit-of-bvand-eric-2
  (implies (and (< 0 size)
                (integerp size) ;drop?
                )
           (equal (getbit 0 (bvand size x y))
                  (bvand 1 x y)))
  :hints (("Goal" :in-theory (enable getbit slice logtail) :cases ((integerp size)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun induct-floor-by-2-floor-by-2-sub-1 (x y n)
   (if (zp n)
       (list x y n)
     (induct-floor-by-2-floor-by-2-sub-1 (floor x 2) (floor y 2) (+ -1 n)))))

;; You can chop one argument of logand down to the size of the other argument
(defthmd logand-of-bvchop
  (implies (and (unsigned-byte-p m x)
                (integerp y))
           (equal (logand x (bvchop m y))
                  (logand x y)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (bvchop ;fl ;FLOOR-TYPE-1 floor-bounded-by-/ MOD-X-Y-=-X+Y-FOR-RATIONALS mod-minus
                                   mod-expt-split FLOOR-WHEN-INTEGERP-OF-QUOTIENT
                                   )
                           ())
           :expand ((LOGAND X (MOD Y (EXPT 2 M)))
                    (LOGAND X Y)
                    (MOD (* 2 (FLOOR Y 2)) (EXPT 2 M)))
           :induct (INDUCT-FLOOR-BY-2-FLOOR-BY-2-SUB-1 x y m))))

(defthm logand-of-bvchop-tighten-free
  (implies (and (unsigned-byte-p freesize x)
                (< freesize size)
                (integerp y)
                (integerp size))
           (equal (logand x (bvchop size y))
                  (logand x (bvchop freesize y))))
  :hints (("Goal" :use (:instance logand-of-bvchop
                                  (y (bvchop size y))
                                  (m freesize)))))


;; You can chop one argument of bvand down to the size of the other argument
(defthmd bvand-tighten-1
  (implies (and (unsigned-byte-p newsize x)
                (< newsize size)
                (natp size)
                (natp newsize))
           (equal (bvand size x y)
                  (bvand newsize x y)))
  :hints (("Goal" :cases ((integerp y))
           :in-theory (enable bvand
                              logand-of-bvchop))))

(defthmd bvand-tighten-2
  (implies (and (unsigned-byte-p newsize y)
                (< newsize size)
                (natp size)
                (natp newsize))
           (equal (bvand size x y)
                  (bvand newsize x y)))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (enable bvand
                              logand-of-bvchop))))

(defthm <=-of-bvand-arg1-linear
  (implies (natp x)
           (<= (bvand size x y) x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable bvand))))

(defthm <=-of-bvand-arg2-linear
  (implies (natp y)
           (<= (bvand size x y) y))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable bvand))))

;; -1 is a mask of all ones
(defthm bvand-of-minus1
  (equal (bvand width -1 x)
         (bvchop width x))
  :hints (("Goal" :in-theory (enable bvand))))

;make versions of these for other ops..
(defthm bvand-subst-arg2
  (implies (and (syntaxp (not (quotep x)))
                (equal (bvchop free x) k)
                (syntaxp (quotep k))
                (<= n free)
                (integerp free))
           (equal (bvand n x y)
                  (bvand n k y)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-subst-arg3
  (implies (and (syntaxp (not (quotep y)))
                (equal (bvchop free y) k)
                (syntaxp (quotep k))
                (<= n free)
                (integerp free))
           (equal (bvand n x y)
                  (bvand n x k)))
  :hints (("Goal" :in-theory (enable bvand))))

;move or drop?
(defun bind-newsize-to-constant-size (x)
  (declare (xargs :guard (and (quotep x)
                              (pseudo-termp x)
                              (natp (unquote x)))))
  (acons 'newsize
         (list 'quote (integer-length (unquote x)))
         nil))

(defthm bvand-of-constant-tighten
   (implies (and (syntaxp (and (quotep k)
                               (< (integer-length (unquote k))
                                  (unquote size))))
                 (bind-free (bind-newsize-to-constant-size k) (newsize))
                 (unsigned-byte-p newsize k)
                 (< newsize size)
                 (natp size)
                 (natp newsize))
            (equal (bvand size k x)
                   (bvand newsize k x)))
   :hints (("Goal" :in-theory (enable bvand-tighten-1))))
