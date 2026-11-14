; bitvec.lisp -- Vectors over F_2 as lists of bits.
;
; Part of an ACL2 formalization of
;   "GPU-Accelerated Search for Fast Matrix Multiplication over F_2"
;   (ALENEX 2027).
;
; A vector over F_2 of length L is a true list of L bits.  Addition is
; componentwise xor.  Matrices (n x n) are vectors of length n*n with
; entry (i,j) stored at index i*n+j, and order-3 tensors are vectors of
; length n^6 (see outer.lisp).

(in-package "ACL2")

(include-book "std/lists/top" :dir :system)
(include-book "kestrel/lists-light/perm" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

;;; ------------------------------------------------------------------
;;; Bits
;;; ------------------------------------------------------------------

(defun bxor (a b)
  (declare (xargs :guard (and (bitp a) (bitp b))))
  (if (eql a b) 0 1))

(defun band (a b)
  (declare (xargs :guard (and (bitp a) (bitp b))))
  (if (and (eql a 1) (eql b 1)) 1 0))

(defthm bitp-of-bxor (bitp (bxor a b)))
(defthm bitp-of-band (bitp (band a b)))

(defthm bxor-commutative
  (implies (and (bitp a) (bitp b))
           (equal (bxor a b) (bxor b a))))

(defthm bxor-associative
  (implies (and (bitp a) (bitp b) (bitp c))
           (equal (bxor (bxor a b) c) (bxor a (bxor b c)))))

(defthm bxor-self (equal (bxor a a) 0))
(defthm bxor-0-left (implies (bitp a) (equal (bxor 0 a) a)))
(defthm bxor-0-right (implies (bitp a) (equal (bxor a 0) a)))
(defthm band-commutative (equal (band a b) (band b a)))
(defthm band-associative (equal (band (band a b) c) (band a (band b c))))
(defthm band-self (implies (bitp a) (equal (band a a) a)))
(defthm band-0-left (equal (band 0 a) 0))
(defthm band-0-right (equal (band a 0) 0))
(defthm band-1-left (implies (bitp a) (equal (band 1 a) a)))
(defthm band-1-right (implies (bitp a) (equal (band a 1) a)))
(defthm band-distributes-over-bxor
  (implies (and (bitp a) (bitp b) (bitp c))
           (equal (band a (bxor b c)) (bxor (band a b) (band a c)))))

;;; ------------------------------------------------------------------
;;; Bit vectors
;;; ------------------------------------------------------------------

(defun bvp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (bitp (car x)) (bvp (cdr x)))))

(defthm bvp-forward-to-true-listp
  (implies (bvp x) (true-listp x))
  :rule-classes :forward-chaining)

(defthm bitp-of-nth-of-bvp
  (implies (and (bvp x) (natp i) (< i (len x)))
           (bitp (nth i x))))

(defthm nth-of-bvp-is-0-or-1
  (implies (and (bvp x) (natp i) (< i (len x)) (not (equal (nth i x) 1)))
           (equal (nth i x) 0)))

(defthm bitp-of-car-of-bvp
  (implies (and (bvp x) (consp x))
           (bitp (car x))))

(defthm bvp-of-cdr (implies (bvp x) (bvp (cdr x))))
(defthm bvp-of-cons (equal (bvp (cons a x)) (and (bitp a) (bvp x))))
(defthm bvp-of-append
  (implies (and (bvp x) (bvp y)) (bvp (append x y))))
(defthm bvp-of-update-nth
  (implies (and (bvp x) (natp i) (< i (len x)) (bitp b))
           (bvp (update-nth i b x))))

;; The zero vector of length L.
(defun bv-zero (L)
  (declare (xargs :guard (natp L)))
  (if (zp L) nil (cons 0 (bv-zero (1- L)))))

(defthm bvp-of-bv-zero (bvp (bv-zero L)))
(defthm len-of-bv-zero (equal (len (bv-zero L)) (nfix L)))
(defun ind2 (i L)
  (if (zp L) (list i L) (ind2 (1- i) (1- L))))

(defthm nth-of-bv-zero
  (equal (nth i (bv-zero L)) (if (< (nfix i) (nfix L)) 0 nil))
  :hints (("Goal" :induct (ind2 i L))))
(defthmd bv-zero-of-append-len
  (implies (and (natp a) (natp b))
           (equal (bv-zero (+ a b))
                  (append (bv-zero a) (bv-zero b))))
  :hints (("Goal" :induct (bv-zero a))))

;; Componentwise xor.  Both arguments are expected to have the same length.
(defun bv+ (x y)
  (declare (xargs :guard (and (bvp x) (bvp y))))
  (cond ((atom x) nil)
        ((atom y) nil)
        (t (cons (bxor (car x) (car y)) (bv+ (cdr x) (cdr y))))))

(defthm bvp-of-bv+ (bvp (bv+ x y)))

(defun ind-nth2 (i x y)
  (if (or (atom x) (atom y)) (list i x y) (ind-nth2 (1- i) (cdr x) (cdr y))))

(defthm len-of-bv+ (equal (len (bv+ x y)) (min (len x) (len y))))

(defthm nth-of-bv+
  (implies (and (natp i) (< i (len x)) (< i (len y)))
           (equal (nth i (bv+ x y)) (bxor (nth i x) (nth i y))))
  :hints (("Goal" :induct (ind-nth2 i x y))))

(defthm bv+-commutative
  (implies (and (bvp x) (bvp y))
           (equal (bv+ x y) (bv+ y x))))

(defthm bv+-associative
  (implies (and (bvp x) (bvp y) (bvp z)
                (equal (len x) (len y)) (equal (len y) (len z)))
           (equal (bv+ (bv+ x y) z) (bv+ x (bv+ y z)))))

(defthm bv+-commutative-2
  (implies (and (bvp x) (bvp y) (bvp z)
                (equal (len x) (len y)) (equal (len y) (len z)))
           (equal (bv+ x (bv+ y z)) (bv+ y (bv+ x z))))
  :hints (("Goal" :use ((:instance bv+-associative (x x) (y y) (z z))
                        (:instance bv+-associative (x y) (y x) (z z)))
                  :in-theory (disable bv+-associative))))

(defthm bv+-self
  (implies (bvp x) (equal (bv+ x x) (bv-zero (len x)))))

(defthm bv+-zero-left
  (implies (and (bvp x) (equal (len x) (nfix L)))
           (equal (bv+ (bv-zero L) x) x)))

(defthm bv+-zero-right
  (implies (and (bvp x) (equal (len x) (nfix L)))
           (equal (bv+ x (bv-zero L)) x)))

(defthm bv+-self-in-middle
  (implies (and (bvp x) (bvp y) (equal (len x) (len y)))
           (equal (bv+ x (bv+ x y)) y))
  :hints (("Goal" :use ((:instance bv+-associative (x x) (y x) (z y)))
                  :in-theory (disable bv+-associative))))

(defthm bv+-cancel-left
  (implies (and (bvp x) (bvp y) (bvp z)
                (equal (len x) (len y)) (equal (len x) (len z)))
           (equal (equal (bv+ x y) (bv+ x z)) (equal y z)))
  :hints (("Goal" :use ((:instance bv+-self-in-middle (x x) (y y))
                        (:instance bv+-self-in-middle (x x) (y z)))
                  :in-theory (disable bv+-self-in-middle))))

(defthm bv+-of-append
  (implies (and (equal (len a) (len c)) (true-listp a) (true-listp c))
           (equal (bv+ (append a b) (append c d))
                  (append (bv+ a c) (bv+ b d)))))

(defthm bv+-equal-zero
  (implies (and (bvp x) (bvp y) (equal (len x) (len y)))
           (equal (equal (bv+ x y) (bv-zero (len x)))
                  (equal x y)))
  :hints (("Goal" :use ((:instance bv+-cancel-left (x x) (y y) (z x)))
                  :in-theory (disable bv+-cancel-left))))

;; Two bit vectors of the same length with the same bits are equal.
(defun bv-diff-index (x y)
  (declare (xargs :guard t))
  (cond ((atom x) 0)
        ((atom y) 0)
        ((equal (car x) (car y)) (1+ (bv-diff-index (cdr x) (cdr y))))
        (t 0)))

(defthm bv-diff-index-witness
  (implies (and (bvp x) (bvp y) (equal (len x) (len y))
                (not (equal x y)))
           (and (< (bv-diff-index x y) (len x))
                (not (equal (nth (bv-diff-index x y) x)
                            (nth (bv-diff-index x y) y))))))

(defthm natp-of-bv-diff-index (natp (bv-diff-index x y))
  :rule-classes :type-prescription)

(defthm bv-extensionality
  (implies (and (bvp x) (bvp y) (equal (len x) (len y))
                (equal (nth (bv-diff-index x y) x)
                       (nth (bv-diff-index x y) y)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :use bv-diff-index-witness)))

;;; ------------------------------------------------------------------
;;; Unit vectors (standard basis)
;;; ------------------------------------------------------------------

;; The vector of length L with a single 1 at position k (if k < L).
(defun unit (L k)
  (declare (xargs :guard (and (natp L) (integerp k))))
  (if (zp L)
      nil
    (cons (if (eql (ifix k) 0) 1 0) (unit (1- L) (1- (ifix k))))))

(defthm bvp-of-unit (bvp (unit L k)))
(defthm len-of-unit (equal (len (unit L k)) (nfix L)))
(defun ind3 (i L k)
  (if (zp L) (list i L k) (ind3 (1- i) (1- L) (1- (ifix k)))))

(defthm nth-of-unit
  (equal (nth i (unit L k))
         (if (< (nfix i) (nfix L))
             (if (equal (nfix i) (ifix k)) 1 0)
           nil))
  :hints (("Goal" :induct (ind3 i L k))))

(defthm unit-not-zero
  (implies (and (natp k) (< k (nfix L)))
           (not (equal (unit L k) (bv-zero L))))
  :hints (("Goal" :use ((:instance nth-of-unit (i k)))
                  :in-theory (disable nth-of-unit))))

(defthm unit-injective
  (implies (and (natp k1) (natp k2) (< k1 (nfix L)) (< k2 (nfix L)))
           (equal (equal (unit L k1) (unit L k2)) (equal k1 k2)))
  :hints (("Goal" :use ((:instance nth-of-unit (i k1) (k k2)))
                  :in-theory (disable nth-of-unit))))

;;; ------------------------------------------------------------------
;;; Weight (number of ones) and lowest set bit
;;; ------------------------------------------------------------------

(defun bv-weight (x)
  (declare (xargs :guard (bvp x)))
  (cond ((atom x) 0)
        ((eql (car x) 1) (1+ (bv-weight (cdr x))))
        (t (bv-weight (cdr x)))))

(defthm natp-of-bv-weight (natp (bv-weight x)) :rule-classes :type-prescription)

(defthm bv-weight-zero-iff
  (implies (bvp x)
           (equal (equal (bv-weight x) 0) (equal x (bv-zero (len x))))))

;; Index of the first 1 in x (len x if none).
(defun bv-first-one (x)
  (declare (xargs :guard (bvp x)))
  (cond ((atom x) 0)
        ((eql (car x) 1) 0)
        (t (1+ (bv-first-one (cdr x))))))

(defthm natp-of-bv-first-one (natp (bv-first-one x)) :rule-classes :type-prescription)

(defthm bv-first-one-witness
  (implies (and (bvp x) (not (equal x (bv-zero (len x)))))
           (and (< (bv-first-one x) (len x))
                (equal (nth (bv-first-one x) x) 1))))

;; Opening unit when its length argument is the length of a consp.
(defthm unit-when-negative
  (implies (and (integerp k) (< k 0))
           (equal (unit L k) (bv-zero L))))

(defthm unit-of-len-when-consp
  (implies (and (syntaxp (variablep x)) (consp x))
           (equal (unit (len x) k)
                  (cons (if (eql (ifix k) 0) 1 0)
                        (unit (len (cdr x)) (1- (ifix k))))))
  :hints (("Goal" :in-theory (disable unit) :expand ((unit (len x) k)))))

(defun ind-xk (x k)
  (if (atom x) (list x k) (ind-xk (cdr x) (1- k))))

;; Adding a unit at a set bit lowers the weight by one.
(defthm bv-weight-of-bv+-unit
  (implies (and (bvp x) (natp k) (< k (len x)) (equal (nth k x) 1))
           (equal (bv-weight (bv+ x (unit (len x) k)))
                  (1- (bv-weight x))))
  :hints (("Goal" :induct (ind-xk x k))))

(defthm bv-weight-of-bv-zero
  (equal (bv-weight (bv-zero L)) 0))

(defthm bv-weight-of-unit
  (implies (and (natp k) (< k (nfix L)))
           (equal (bv-weight (unit L k)) 1))
  :hints (("Goal" :induct (ind3 k L k))))

;; A nonzero vector of weight 1 is a unit at its first set bit.
(defthm bv-weight-one-is-unit
  (implies (and (bvp x) (equal (bv-weight x) 1))
           (equal (unit (len x) (bv-first-one x)) x))
  :hints (("Goal" :induct (bv-first-one x))))

;;; ------------------------------------------------------------------
;;; Lists of vectors of a common length, and their sums
;;; ------------------------------------------------------------------

(defun bv-listp (L lst)
  (declare (xargs :guard (natp L)))
  (if (atom lst)
      (null lst)
    (and (bvp (car lst))
         (equal (len (car lst)) (nfix L))
         (bv-listp L (cdr lst)))))

(defthm bv-listp-of-append
  (implies (true-listp x)
           (equal (bv-listp L (append x y))
                  (and (bv-listp L x) (bv-listp L y))))
  :hints (("Goal" :induct (bv-listp L x))))

(defthm bv-listp-of-cons
  (equal (bv-listp L (cons a x))
         (and (bvp a) (equal (len a) (nfix L)) (bv-listp L x))))

(defthm bv-listp-of-remove1
  (implies (bv-listp L x) (bv-listp L (remove1-equal a x)))
  :hints (("Goal" :in-theory (enable remove1-equal) :induct (remove1-equal a x))))

(defthm bv-listp-member
  (implies (and (bv-listp L x) (member-equal a x))
           (and (bvp a) (equal (len a) (nfix L))))
  :hints (("Goal" :induct (bv-listp L x))))

(defthm bv-listp-forward-to-true-listp
  (implies (bv-listp L x) (true-listp x))
  :rule-classes :forward-chaining)

(defun bv-sum (L lst)
  (declare (xargs :guard (and (natp L) (bv-listp L lst))))
  (if (atom lst)
      (bv-zero L)
    (bv+ (car lst) (bv-sum L (cdr lst)))))

(defthm bvp-of-bv-sum (bvp (bv-sum L lst)))

(defthm len-of-bv-sum
  (implies (bv-listp L lst)
           (equal (len (bv-sum L lst)) (nfix L))))

(defthm bv-sum-of-append
  (implies (and (bv-listp L x) (bv-listp L y))
           (equal (bv-sum L (append x y))
                  (bv+ (bv-sum L x) (bv-sum L y))))
  :hints (("Goal" :induct (bv-listp L x))))

(defthm bv-sum-of-remove1
  (implies (and (bv-listp L x) (member-equal a x))
           (equal (bv-sum L (remove1-equal a x))
                  (bv+ a (bv-sum L x))))
  :hints (("Goal" :in-theory (enable remove1-equal) :induct (remove1-equal a x))))

(defthm true-listp-of-remove1-equal-when-true-listp
  (implies (true-listp y) (true-listp (remove1-equal a y)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm bv-listp-of-remove1-converse
  (implies (and (member-equal a y) (bvp a) (equal (len a) (nfix L))
                (true-listp y)
                (bv-listp L (remove1-equal a y)))
           (bv-listp L y))
  :hints (("Goal" :in-theory (enable remove1-equal) :induct (remove1-equal a y))))

(defthm bv-listp-when-perm
  (implies (and (perm x y) (bv-listp L x) (true-listp y))
           (bv-listp L y))
  :hints (("Goal" :in-theory (enable perm) :induct (perm x y))))

(defthm bv-sum-when-perm
  (implies (and (perm x y) (bv-listp L x) (bv-listp L y))
           (equal (bv-sum L x) (bv-sum L y)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable perm) :induct (perm x y))))

;; The sum of a list all of whose members equal v is v or zero.
(defun all-equal-to (v lst)
  (declare (xargs :guard t))
  (if (atom lst)
      t
    (and (equal (car lst) v) (all-equal-to v (cdr lst)))))

(defun even-lenp (lst)
  (declare (xargs :guard t))
  (if (atom lst) t (not (even-lenp (cdr lst)))))

(defthm bv-sum-when-all-equal-to
  (implies (and (bv-listp L lst) (all-equal-to v lst))
           (equal (bv-sum L lst)
                  (if (even-lenp lst) (bv-zero L) v)))
  :hints (("Goal" :induct (bv-listp L lst))))

;;; ------------------------------------------------------------------
;;; Cancelling duplicate pairs (over F_2, v + v = 0)
;;; ------------------------------------------------------------------

;; Remove pairs of equal elements from a list.  The sum is unchanged and
;; the result has no duplicates.
(defthm len-of-remove1-equal-when-member
  (implies (member-equal a x)
           (equal (len (remove1-equal a x)) (1- (len x))))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defun cancel-dups (lst)
  (declare (xargs :guard (true-listp lst)
                  :measure (len lst)))
  (cond ((atom lst) nil)
        ((member-equal (car lst) (cdr lst))
         (cancel-dups (remove1-equal (car lst) (cdr lst))))
        (t (cons (car lst) (cancel-dups (cdr lst))))))

(defthm bv-listp-of-cancel-dups
  (implies (bv-listp L lst) (bv-listp L (cancel-dups lst)))
  :hints (("Goal" :induct (cancel-dups lst))))

(defthm bv-sum-of-cancel-dups
  (implies (bv-listp L lst)
           (equal (bv-sum L (cancel-dups lst)) (bv-sum L lst)))
  :hints (("Goal" :induct (cancel-dups lst))))

(defthm member-of-cancel-dups
  (implies (member-equal a (cancel-dups lst))
           (member-equal a lst))
  :hints (("Goal" :induct (cancel-dups lst))))

(defthm no-duplicatesp-of-cancel-dups
  (no-duplicatesp-equal (cancel-dups lst))
  :hints (("Goal" :induct (cancel-dups lst))))

(defthm subsetp-of-cancel-dups
  (subsetp-equal (cancel-dups lst) lst)
  :hints (("Goal" :induct (cancel-dups lst))))
