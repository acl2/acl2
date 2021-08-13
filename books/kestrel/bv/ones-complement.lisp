; Formalization of one's complement arithmetic
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvnot")
(include-book "bvplus")
(include-book "bvuminus") ;make local?
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-mod-expt" :dir :system))
(local (include-book "meta/meta-plus-lessp" :dir :system))
(local (include-book "meta/meta-plus-equal" :dir :system))

;; (thm
;;  (implies (posp size)
;;           (equal (FLOOR (- (EXPT 2 (+ 1 SIZE)))
;;                         (EXPT 2 (+ -1 SIZE)))
;;                  -4))
;;  :hints (("Goal" :in-theory (enable FLOOR-WHEN-MOD-0
;;                                     EXPT-OF-+))))

;; (defthm expt-of-+-linear
;;   (implies (and (natp n1)
;;                 (natp n2))
;;            (< (expt 2 n1)
;;               (expt 2 (+ n1 n2))))
;;   :rule-classes :linear
;;   :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm expt-of-+-of-1-linear
  (implies (natp n1)
           (< (expt 2 n1)
              (expt 2 (+ 1 n1))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm expt-of-+-of--1-linear
  (implies (natp n1)
           (< (expt 2 (+ -1 n1))
              (expt 2 n1)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm expt-of-+-of--1-linear-2
  (implies (natp n)
           (= (+ (expt 2 (+ -1 n))
                 (expt 2 (+ -1 n)))
              (expt 2 n)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthmd bvnot-becomes-bvplus-of--1-and-bvuminus
  (equal (bvnot size x)
         (bvplus size -1 (bvuminus size x)))
  :hints (("Goal" :in-theory (enable bvuminus bvnot bvminus lognot bvplus))))

(local (in-theory (disable bvuminus)))

(defthmd unsigned-byte-p-of-+-of-1-and-+
  (implies (and (syntaxp (not (quotep size))) ;prevent matching (+ 1 size) with a constant
                (unsigned-byte-p size x)
                (unsigned-byte-p size y))
           (unsigned-byte-p (+ 1 size) (+ x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p
                                     expt-of-+))))

(defthmd bvplus-of-+-of-1-split
  (implies (and (unsigned-byte-p size x)
                (unsigned-byte-p size y))
           (equal (BVPLUS (+ 1 SIZE) X Y)
                  (if (<= (expt 2 size) (+ x y))
                      (+ (expt 2 size)
                         (BVPLUS SIZE X Y))
                    (BVPLUS SIZE X Y))))
  :hints (("Goal" :in-theory (enable bvplus unsigned-byte-p-of-+-of-1-and-+ BVCHOP-OF-SUM-CASES))))

(defthm <-of-expt-cancel-1
  (implies (posp size)
           (equal (< (EXPT 2 (+ -1 SIZE)) (+ X Y (EXPT 2 SIZE)))
                  (< 0 (+ x y (EXPT 2 (+ -1 SIZE))))))
  :hints (("Goal" :cases ((< 0 (+ x y (EXPT 2 (+ -1 SIZE))))))))

;;;
;;; End of library material
;;;

;; Computes the one's complement of X, by inverting all of its bits, turning
;; 0s into 1s and vice versa.
(defund ones-complement (size x)
  (declare (xargs :guard (and (natp size)
                              (unsigned-byte-p size x))))
  (bvnot size x))

(defthm unsigned-byte-p-of-ones-complement
  (equal (unsigned-byte-p size (ones-complement size x))
         (natp size))
  :hints (("Goal" :in-theory (enable ones-complement))))

;; Converts X, interpreted as a one's complement number, into the integer it
;; represents.
(defund from-ones-complement (size x)
  (declare (xargs :guard (and (posp size)
                              (unsigned-byte-p size x))))
  (let ((x (mbe :logic (bvchop size x) :exec x))) ; just in case
    (if (< x (expt 2 (+ -1 size))) ;; (equal 0 (getbit (+ -1 size) x))
        ;; positive value:
        x
      ;; negative value (flip the bits and negate):
      (- (ones-complement size x)))))

;; Checks whether the integer X is representable as a one's complement number
;; with SIZE bits.
(defund representable-as-ones-complementp (size x)
  (declare (xargs :guard (and (posp size)
                              (integerp x))))
  (and (<= (- (+ -1 (expt 2 (+ -1 size))))
           x)
       (<= x
           (+ -1 (expt 2 (+ -1 size))))))

(defthm representable-as-ones-complementp-from-ones-complement
  (implies (and (posp size)
                (unsigned-byte-p size x))
           (representable-as-ones-complementp size (from-ones-complement size x)))
  :hints (("Goal" :in-theory (enable representable-as-ones-complementp
                                     from-ones-complement
                                     ones-complement
                                     unsigned-byte-p
                                     bvnot
                                     lognot
                                     bvchop-of-sum-cases))))

;; Convert the integer X to one's complement form.  If x is 0, this returns
;; positive 0.
(defund to-ones-complement (size x)
  (declare (xargs :guard (and (posp size)
                              (integerp x)
                              (representable-as-ones-complementp size x))))
  (if (<= 0 x)
      x
    (bvnot size (- x))))

(defthm bvnot-of-+-of-1-and-expt-same
  (equal (bvnot size (+ -1 (expt 2 size)))
         0)
  :hints (("Goal" :in-theory (enable bvnot lognot))))

;todo: make a mod-when-negative-and-small
(defthmd bvchop-when-negative-and-small
  (IMPLIES (AND (< X 0) ; x is negative
                (INTEGERP SIZE)
                (< 0 SIZE)
                (INTEGERP X)
                (< (- (EXPT 2 (+ -1 SIZE))) x)
                )
           (EQUAL (BVCHOP SIZE X)
                  (+ (expt 2 size) x)))
  :hints (("Goal" :in-theory (enable bvchop mod FLOOR-WHEN-NEGATIVE-AND-SMALL))))

(defthm bvnot-of--
  (implies (and (integerp size)
                (< 0 size)
                (integerp x))
           (equal (bvnot size (- x))
                  (if (equal (bvchop size x) 0)
                      (+ -1 (expt 2 size))
                    (+ (bvchop size x) -1))))
  :hints (("Goal" :in-theory (enable bvnot lognot bvchop MOD-SUM-CASES))))

(defthm from-ones-complement-of-to-ones-complement
  (implies (and (posp size)
                (integerp x)
                (representable-as-ones-complementp size x))
           (equal (from-ones-complement size (to-ones-complement size x))
                  x))
  :hints (("Goal" :in-theory (enable from-ones-complement
                                     to-ones-complement
                                     representable-as-ones-complementp
                                     ones-complement
                                     bvnot
                                     lognot
                                     bvchop-of-sum-cases
                                     unsigned-byte-p
                                     bvchop-when-negative-and-small))))

;; The one's complement representation of "negative 0" (all ones).
(defun negative-zero (size)
  (declare (xargs :guard (posp size)))
  (+ -1 (expt 2 size)))

(defthm to-ones-complement-of-from-ones-complement
  (implies (and ;; (posp size)
                (unsigned-byte-p size x)
                (not (equal x (negative-zero size)))
                )
           (equal (to-ones-complement size (from-ones-complement size x))
                  x))
  :hints (("Goal" :in-theory (enable from-ones-complement
                                     to-ones-complement
                                     representable-as-ones-complementp
                                     ones-complement
                                     bvnot
                                     lognot
                                     bvchop-of-sum-cases
                                     unsigned-byte-p
                                     bvchop-when-negative-and-small))))

;; Turning negative 0 to an integer and then back into a ones complement value
;; changes it to the regular 0.
(thm
 (equal (to-ones-complement size (from-ones-complement size (negative-zero size)))
        0)
 :hints (("Goal" :in-theory (enable from-ones-complement
                                    to-ones-complement
                                    representable-as-ones-complementp
                                    ones-complement
                                    bvnot
                                    lognot
                                    bvchop-of-sum-cases
                                    unsigned-byte-p
                                    bvchop-when-negative-and-small))))

;; Computes the one's complement sum of X and Y.
;; TODO: Define as converting, adding, then converting back?
(defund bvplus1c (size x y)
  (declare (xargs :guard (and (natp size)
                              (unsigned-byte-p size x)
                              (unsigned-byte-p size y))))
  (let* ((x (mbe :logic (bvchop size x) :exec x))
         (y (mbe :logic (bvchop size y) :exec y))
         (sum (+ x y)))
    (if (<= (expt 2 size) sum)
        ;; end-around carry:
        (bvchop size (+ 1 sum))
      ;; already fits in SIZE bits:
      sum)))

(defthm unsigned-byte-p-of-bvplus1c
  (implies (natp size)
           (unsigned-byte-p size (bvplus1c size x y)))
  :hints (("Goal" :in-theory (enable bvplus1c
                                     unsigned-byte-p))))

;; Prove correctness of bvplus1c:
(defthmd bvplus1c-correct
  (implies (and (unsigned-byte-p size x)
                (unsigned-byte-p size y)
                ;; (posp size)
                ;; the sum is representable:
                (representable-as-ones-complementp
                 size
                 (+ (from-ones-complement size x)
                    (from-ones-complement size y))))
           (equal (from-ones-complement size (bvplus1c size x y))
                  (+ (from-ones-complement size x)
                     (from-ones-complement size y))))
  :hints (("Goal" :in-theory (enable bvplus1c
                                     from-ones-complement
                                     ones-complement
                                     representable-as-ones-complementp
                                     bvnot-becomes-bvplus-of--1-and-bvuminus
                                     bvplus-of-+-of-1-split
                                     bvuminus
                                     bvminus
                                     bvplus
                                     bvchop-of-sum-cases
                                     unsigned-byte-p))))

(defthm +-of-*-of-1/2-and-*-of-1/2-same
  (implies (acl2-numberp x)
           (equal (+ (* 1/2 X) (* 1/2 X))
                  x)))

;; Check whether X is equal to positive 0 (all zeros) or negative 0 (all ones).
(defund ones-complement-zerop (size x)
  (declare (xargs :guard (and (natp size)
                              (unsigned-byte-p size x))))
  (or (equal x 0)
      (equal x (+ -1 (expt 2 size)))))

;; Check whether X and Y are numerically equal
(defund ones-complement-equal (size x y)
  (declare (xargs :guard (and (posp size)
                              (unsigned-byte-p size x)
                              (unsigned-byte-p size y))))
  (equal (from-ones-complement size x)
         (from-ones-complement size y)))

(defthmd bvplus1c-correct-2
  (implies (and (unsigned-byte-p size x)
                (unsigned-byte-p size y)
                (posp size)
                ;; the sum is representable:
                ;; (representable-as-ones-complementp
                ;;  size
                ;;  (+ (from-ones-complement size x)
                ;;     (from-ones-complement size y)))
                )
           ;; Can't use equal here, because bvplus1c might return negative 0 whereas
           ;; to-ones-complement always chooses positive 0 for a 0 value:
           (ones-complement-equal size
                                  (bvplus1c size x y)
                                  (to-ones-complement size
                                                      (+ (from-ones-complement size x)
                                                         (from-ones-complement size y)))))
  :hints (("Goal" :in-theory (enable bvplus1c
                                     to-ones-complement
                                     from-ones-complement
                                     ones-complement
                                     representable-as-ones-complementp
                                     bvnot-becomes-bvplus-of--1-and-bvuminus
                                     bvplus-of-+-of-1-split
                                     bvuminus
                                     bvminus
                                     bvplus
                                     bvchop-of-sum-cases
                                     unsigned-byte-p
                                     ONES-COMPLEMENT-EQUAL
                                     ONES-COMPLEMENT-ZEROP))))

 ;; :hints (("Goal" :in-theory (e/d (from-ones-complement
 ;;                                  bvplus1c
 ;;                                  ONES-COMPLEMENT
 ;;                                  bvplus
 ;;                                  BVCHOP-OF-SUM-CASES
 ;;                                  getbit
 ;;                                  SLICE
 ;;                                  BVNOT
 ;;                                  lognot
 ;;                                  LOGTAIL$INLINE
 ;;                                  FLOOR-OF-SUM
 ;;                                  UNSIGNED-BYTE-P
 ;;                                  bvchop
 ;;                                  expt-of-+)
 ;;                                 (BVCHOP-1-BECOMES-GETBIT
 ;;                                  slice-BECOMES-GETBIT
 ;;                                  BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))
