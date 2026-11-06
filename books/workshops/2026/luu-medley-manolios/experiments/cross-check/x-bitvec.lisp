; x-bitvec.lisp -- MECHANICAL RENAMING (prefix x-) of ../unassisted/bitvec.lisp
; produced by rename.py in this directory; do not edit by hand.
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

(defun x-bxor (a b)
  (declare (xargs :guard (and (bitp a) (bitp b))))
  (if (eql a b) 0 1))

(defun x-band (a b)
  (declare (xargs :guard (and (bitp a) (bitp b))))
  (if (and (eql a 1) (eql b 1)) 1 0))

(defthm x-bitp-of-bxor (bitp (x-bxor a b)))
(defthm x-bitp-of-band (bitp (x-band a b)))

(defthm x-bxor-commutative
  (implies (and (bitp a) (bitp b))
           (equal (x-bxor a b) (x-bxor b a))))

(defthm x-bxor-associative
  (implies (and (bitp a) (bitp b) (bitp c))
           (equal (x-bxor (x-bxor a b) c) (x-bxor a (x-bxor b c)))))

(defthm x-bxor-self (equal (x-bxor a a) 0))
(defthm x-bxor-0-left (implies (bitp a) (equal (x-bxor 0 a) a)))
(defthm x-bxor-0-right (implies (bitp a) (equal (x-bxor a 0) a)))
(defthm x-band-commutative (equal (x-band a b) (x-band b a)))
(defthm x-band-associative (equal (x-band (x-band a b) c) (x-band a (x-band b c))))
(defthm x-band-self (implies (bitp a) (equal (x-band a a) a)))
(defthm x-band-0-left (equal (x-band 0 a) 0))
(defthm x-band-0-right (equal (x-band a 0) 0))
(defthm x-band-1-left (implies (bitp a) (equal (x-band 1 a) a)))
(defthm x-band-1-right (implies (bitp a) (equal (x-band a 1) a)))
(defthm x-band-distributes-over-bxor
  (implies (and (bitp a) (bitp b) (bitp c))
           (equal (x-band a (x-bxor b c)) (x-bxor (x-band a b) (x-band a c)))))

;;; ------------------------------------------------------------------
;;; Bit vectors
;;; ------------------------------------------------------------------

(defun x-bvp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (bitp (car x)) (x-bvp (cdr x)))))

(defthm x-bvp-forward-to-true-listp
  (implies (x-bvp x) (true-listp x))
  :rule-classes :forward-chaining)

(defthm x-bitp-of-nth-of-bvp
  (implies (and (x-bvp x) (natp i) (< i (len x)))
           (bitp (nth i x))))

(defthm x-nth-of-bvp-is-0-or-1
  (implies (and (x-bvp x) (natp i) (< i (len x)) (not (equal (nth i x) 1)))
           (equal (nth i x) 0)))

(defthm x-bitp-of-car-of-bvp
  (implies (and (x-bvp x) (consp x))
           (bitp (car x))))

(defthm x-bvp-of-cdr (implies (x-bvp x) (x-bvp (cdr x))))
(defthm x-bvp-of-cons (equal (x-bvp (cons a x)) (and (bitp a) (x-bvp x))))
(defthm x-bvp-of-append
  (implies (and (x-bvp x) (x-bvp y)) (x-bvp (append x y))))
(defthm x-bvp-of-update-nth
  (implies (and (x-bvp x) (natp i) (< i (len x)) (bitp b))
           (x-bvp (update-nth i b x))))

;; The zero vector of length L.
(defun x-bv-zero (L)
  (declare (xargs :guard (natp L)))
  (if (zp L) nil (cons 0 (x-bv-zero (1- L)))))

(defthm x-bvp-of-bv-zero (x-bvp (x-bv-zero L)))
(defthm x-len-of-bv-zero (equal (len (x-bv-zero L)) (nfix L)))
(defun x-ind2 (i L)
  (if (zp L) (list i L) (x-ind2 (1- i) (1- L))))

(defthm x-nth-of-bv-zero
  (equal (nth i (x-bv-zero L)) (if (< (nfix i) (nfix L)) 0 nil))
  :hints (("Goal" :induct (x-ind2 i L))))
(defthmd x-bv-zero-of-append-len
  (implies (and (natp a) (natp b))
           (equal (x-bv-zero (+ a b))
                  (append (x-bv-zero a) (x-bv-zero b))))
  :hints (("Goal" :induct (x-bv-zero a))))

;; Componentwise xor.  Both arguments are expected to have the same length.
(defun x-bv+ (x y)
  (declare (xargs :guard (and (x-bvp x) (x-bvp y))))
  (cond ((atom x) nil)
        ((atom y) nil)
        (t (cons (x-bxor (car x) (car y)) (x-bv+ (cdr x) (cdr y))))))

(defthm x-bvp-of-bv+ (x-bvp (x-bv+ x y)))

(defun x-ind-nth2 (i x y)
  (if (or (atom x) (atom y)) (list i x y) (x-ind-nth2 (1- i) (cdr x) (cdr y))))

(defthm x-len-of-bv+ (equal (len (x-bv+ x y)) (min (len x) (len y))))

(defthm x-nth-of-bv+
  (implies (and (natp i) (< i (len x)) (< i (len y)))
           (equal (nth i (x-bv+ x y)) (x-bxor (nth i x) (nth i y))))
  :hints (("Goal" :induct (x-ind-nth2 i x y))))

(defthm x-bv+-commutative
  (implies (and (x-bvp x) (x-bvp y))
           (equal (x-bv+ x y) (x-bv+ y x))))

(defthm x-bv+-associative
  (implies (and (x-bvp x) (x-bvp y) (x-bvp z)
                (equal (len x) (len y)) (equal (len y) (len z)))
           (equal (x-bv+ (x-bv+ x y) z) (x-bv+ x (x-bv+ y z)))))

(defthm x-bv+-commutative-2
  (implies (and (x-bvp x) (x-bvp y) (x-bvp z)
                (equal (len x) (len y)) (equal (len y) (len z)))
           (equal (x-bv+ x (x-bv+ y z)) (x-bv+ y (x-bv+ x z))))
  :hints (("Goal" :use ((:instance x-bv+-associative (x x) (y y) (z z))
                        (:instance x-bv+-associative (x y) (y x) (z z)))
                  :in-theory (disable x-bv+-associative))))

(defthm x-bv+-self
  (implies (x-bvp x) (equal (x-bv+ x x) (x-bv-zero (len x)))))

(defthm x-bv+-zero-left
  (implies (and (x-bvp x) (equal (len x) (nfix L)))
           (equal (x-bv+ (x-bv-zero L) x) x)))

(defthm x-bv+-zero-right
  (implies (and (x-bvp x) (equal (len x) (nfix L)))
           (equal (x-bv+ x (x-bv-zero L)) x)))

(defthm x-bv+-self-in-middle
  (implies (and (x-bvp x) (x-bvp y) (equal (len x) (len y)))
           (equal (x-bv+ x (x-bv+ x y)) y))
  :hints (("Goal" :use ((:instance x-bv+-associative (x x) (y x) (z y)))
                  :in-theory (disable x-bv+-associative))))

(defthm x-bv+-cancel-left
  (implies (and (x-bvp x) (x-bvp y) (x-bvp z)
                (equal (len x) (len y)) (equal (len x) (len z)))
           (equal (equal (x-bv+ x y) (x-bv+ x z)) (equal y z)))
  :hints (("Goal" :use ((:instance x-bv+-self-in-middle (x x) (y y))
                        (:instance x-bv+-self-in-middle (x x) (y z)))
                  :in-theory (disable x-bv+-self-in-middle))))

(defthm x-bv+-of-append
  (implies (and (equal (len a) (len c)) (true-listp a) (true-listp c))
           (equal (x-bv+ (append a b) (append c d))
                  (append (x-bv+ a c) (x-bv+ b d)))))

(defthm x-bv+-equal-zero
  (implies (and (x-bvp x) (x-bvp y) (equal (len x) (len y)))
           (equal (equal (x-bv+ x y) (x-bv-zero (len x)))
                  (equal x y)))
  :hints (("Goal" :use ((:instance x-bv+-cancel-left (x x) (y y) (z x)))
                  :in-theory (disable x-bv+-cancel-left))))

;; Two bit vectors of the same length with the same bits are equal.
(defun x-bv-diff-index (x y)
  (declare (xargs :guard t))
  (cond ((atom x) 0)
        ((atom y) 0)
        ((equal (car x) (car y)) (1+ (x-bv-diff-index (cdr x) (cdr y))))
        (t 0)))

(defthm x-bv-diff-index-witness
  (implies (and (x-bvp x) (x-bvp y) (equal (len x) (len y))
                (not (equal x y)))
           (and (< (x-bv-diff-index x y) (len x))
                (not (equal (nth (x-bv-diff-index x y) x)
                            (nth (x-bv-diff-index x y) y))))))

(defthm x-natp-of-bv-diff-index (natp (x-bv-diff-index x y))
  :rule-classes :type-prescription)

(defthm x-bv-extensionality
  (implies (and (x-bvp x) (x-bvp y) (equal (len x) (len y))
                (equal (nth (x-bv-diff-index x y) x)
                       (nth (x-bv-diff-index x y) y)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :use x-bv-diff-index-witness)))

;;; ------------------------------------------------------------------
;;; Unit vectors (standard basis)
;;; ------------------------------------------------------------------

;; The vector of length L with a single 1 at position k (if k < L).
(defun x-unit (L k)
  (declare (xargs :guard (and (natp L) (integerp k))))
  (if (zp L)
      nil
    (cons (if (eql (ifix k) 0) 1 0) (x-unit (1- L) (1- (ifix k))))))

(defthm x-bvp-of-unit (x-bvp (x-unit L k)))
(defthm x-len-of-unit (equal (len (x-unit L k)) (nfix L)))
(defun x-ind3 (i L k)
  (if (zp L) (list i L k) (x-ind3 (1- i) (1- L) (1- (ifix k)))))

(defthm x-nth-of-unit
  (equal (nth i (x-unit L k))
         (if (< (nfix i) (nfix L))
             (if (equal (nfix i) (ifix k)) 1 0)
           nil))
  :hints (("Goal" :induct (x-ind3 i L k))))

(defthm x-unit-not-zero
  (implies (and (natp k) (< k (nfix L)))
           (not (equal (x-unit L k) (x-bv-zero L))))
  :hints (("Goal" :use ((:instance x-nth-of-unit (i k)))
                  :in-theory (disable x-nth-of-unit))))

(defthm x-unit-injective
  (implies (and (natp k1) (natp k2) (< k1 (nfix L)) (< k2 (nfix L)))
           (equal (equal (x-unit L k1) (x-unit L k2)) (equal k1 k2)))
  :hints (("Goal" :use ((:instance x-nth-of-unit (i k1) (k k2)))
                  :in-theory (disable x-nth-of-unit))))

;;; ------------------------------------------------------------------
;;; Weight (number of ones) and lowest set bit
;;; ------------------------------------------------------------------

(defun x-bv-weight (x)
  (declare (xargs :guard (x-bvp x)))
  (cond ((atom x) 0)
        ((eql (car x) 1) (1+ (x-bv-weight (cdr x))))
        (t (x-bv-weight (cdr x)))))

(defthm x-natp-of-bv-weight (natp (x-bv-weight x)) :rule-classes :type-prescription)

(defthm x-bv-weight-zero-iff
  (implies (x-bvp x)
           (equal (equal (x-bv-weight x) 0) (equal x (x-bv-zero (len x))))))

;; Index of the first 1 in x (len x if none).
(defun x-bv-first-one (x)
  (declare (xargs :guard (x-bvp x)))
  (cond ((atom x) 0)
        ((eql (car x) 1) 0)
        (t (1+ (x-bv-first-one (cdr x))))))

(defthm x-natp-of-bv-first-one (natp (x-bv-first-one x)) :rule-classes :type-prescription)

(defthm x-bv-first-one-witness
  (implies (and (x-bvp x) (not (equal x (x-bv-zero (len x)))))
           (and (< (x-bv-first-one x) (len x))
                (equal (nth (x-bv-first-one x) x) 1))))

;; Opening unit when its length argument is the length of a consp.
(defthm x-unit-when-negative
  (implies (and (integerp k) (< k 0))
           (equal (x-unit L k) (x-bv-zero L))))

(defthm x-unit-of-len-when-consp
  (implies (and (syntaxp (variablep x)) (consp x))
           (equal (x-unit (len x) k)
                  (cons (if (eql (ifix k) 0) 1 0)
                        (x-unit (len (cdr x)) (1- (ifix k))))))
  :hints (("Goal" :in-theory (disable x-unit) :expand ((x-unit (len x) k)))))

(defun x-ind-xk (x k)
  (if (atom x) (list x k) (x-ind-xk (cdr x) (1- k))))

;; Adding a unit at a set bit lowers the weight by one.
(defthm x-bv-weight-of-bv+-unit
  (implies (and (x-bvp x) (natp k) (< k (len x)) (equal (nth k x) 1))
           (equal (x-bv-weight (x-bv+ x (x-unit (len x) k)))
                  (1- (x-bv-weight x))))
  :hints (("Goal" :induct (x-ind-xk x k))))

(defthm x-bv-weight-of-bv-zero
  (equal (x-bv-weight (x-bv-zero L)) 0))

(defthm x-bv-weight-of-unit
  (implies (and (natp k) (< k (nfix L)))
           (equal (x-bv-weight (x-unit L k)) 1))
  :hints (("Goal" :induct (x-ind3 k L k))))

;; A nonzero vector of weight 1 is a unit at its first set bit.
(defthm x-bv-weight-one-is-unit
  (implies (and (x-bvp x) (equal (x-bv-weight x) 1))
           (equal (x-unit (len x) (x-bv-first-one x)) x))
  :hints (("Goal" :induct (x-bv-first-one x))))

;;; ------------------------------------------------------------------
;;; Lists of vectors of a common length, and their sums
;;; ------------------------------------------------------------------

(defun x-bv-listp (L lst)
  (declare (xargs :guard (natp L)))
  (if (atom lst)
      (null lst)
    (and (x-bvp (car lst))
         (equal (len (car lst)) (nfix L))
         (x-bv-listp L (cdr lst)))))

(defthm x-bv-listp-of-append
  (implies (true-listp x)
           (equal (x-bv-listp L (append x y))
                  (and (x-bv-listp L x) (x-bv-listp L y))))
  :hints (("Goal" :induct (x-bv-listp L x))))

(defthm x-bv-listp-of-cons
  (equal (x-bv-listp L (cons a x))
         (and (x-bvp a) (equal (len a) (nfix L)) (x-bv-listp L x))))

(defthm x-bv-listp-of-remove1
  (implies (x-bv-listp L x) (x-bv-listp L (remove1-equal a x)))
  :hints (("Goal" :in-theory (enable remove1-equal) :induct (remove1-equal a x))))

(defthm x-bv-listp-member
  (implies (and (x-bv-listp L x) (member-equal a x))
           (and (x-bvp a) (equal (len a) (nfix L))))
  :hints (("Goal" :induct (x-bv-listp L x))))

(defthm x-bv-listp-forward-to-true-listp
  (implies (x-bv-listp L x) (true-listp x))
  :rule-classes :forward-chaining)

(defun x-bv-sum (L lst)
  (declare (xargs :guard (and (natp L) (x-bv-listp L lst))))
  (if (atom lst)
      (x-bv-zero L)
    (x-bv+ (car lst) (x-bv-sum L (cdr lst)))))

(defthm x-bvp-of-bv-sum (x-bvp (x-bv-sum L lst)))

(defthm x-len-of-bv-sum
  (implies (x-bv-listp L lst)
           (equal (len (x-bv-sum L lst)) (nfix L))))

(defthm x-bv-sum-of-append
  (implies (and (x-bv-listp L x) (x-bv-listp L y))
           (equal (x-bv-sum L (append x y))
                  (x-bv+ (x-bv-sum L x) (x-bv-sum L y))))
  :hints (("Goal" :induct (x-bv-listp L x))))

(defthm x-bv-sum-of-remove1
  (implies (and (x-bv-listp L x) (member-equal a x))
           (equal (x-bv-sum L (remove1-equal a x))
                  (x-bv+ a (x-bv-sum L x))))
  :hints (("Goal" :in-theory (enable remove1-equal) :induct (remove1-equal a x))))

(defthm x-true-listp-of-remove1-equal-when-true-listp
  (implies (true-listp y) (true-listp (remove1-equal a y)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm x-bv-listp-of-remove1-converse
  (implies (and (member-equal a y) (x-bvp a) (equal (len a) (nfix L))
                (true-listp y)
                (x-bv-listp L (remove1-equal a y)))
           (x-bv-listp L y))
  :hints (("Goal" :in-theory (enable remove1-equal) :induct (remove1-equal a y))))

(defthm x-bv-listp-when-perm
  (implies (and (perm x y) (x-bv-listp L x) (true-listp y))
           (x-bv-listp L y))
  :hints (("Goal" :in-theory (enable perm) :induct (perm x y))))

(defthm x-bv-sum-when-perm
  (implies (and (perm x y) (x-bv-listp L x) (x-bv-listp L y))
           (equal (x-bv-sum L x) (x-bv-sum L y)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable perm) :induct (perm x y))))

;; The sum of a list all of whose members equal v is v or zero.
(defun x-all-equal-to (v lst)
  (declare (xargs :guard t))
  (if (atom lst)
      t
    (and (equal (car lst) v) (x-all-equal-to v (cdr lst)))))

(defun x-even-lenp (lst)
  (declare (xargs :guard t))
  (if (atom lst) t (not (x-even-lenp (cdr lst)))))

(defthm x-bv-sum-when-all-equal-to
  (implies (and (x-bv-listp L lst) (x-all-equal-to v lst))
           (equal (x-bv-sum L lst)
                  (if (x-even-lenp lst) (x-bv-zero L) v)))
  :hints (("Goal" :induct (x-bv-listp L lst))))

;;; ------------------------------------------------------------------
;;; Cancelling duplicate pairs (over F_2, v + v = 0)
;;; ------------------------------------------------------------------

;; Remove pairs of equal elements from a list.  The sum is unchanged and
;; the result has no duplicates.
(defthm x-len-of-remove1-equal-when-member
  (implies (member-equal a x)
           (equal (len (remove1-equal a x)) (1- (len x))))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defun x-cancel-dups (lst)
  (declare (xargs :guard (true-listp lst)
                  :measure (len lst)))
  (cond ((atom lst) nil)
        ((member-equal (car lst) (cdr lst))
         (x-cancel-dups (remove1-equal (car lst) (cdr lst))))
        (t (cons (car lst) (x-cancel-dups (cdr lst))))))

(defthm x-bv-listp-of-cancel-dups
  (implies (x-bv-listp L lst) (x-bv-listp L (x-cancel-dups lst)))
  :hints (("Goal" :induct (x-cancel-dups lst))))

(defthm x-bv-sum-of-cancel-dups
  (implies (x-bv-listp L lst)
           (equal (x-bv-sum L (x-cancel-dups lst)) (x-bv-sum L lst)))
  :hints (("Goal" :induct (x-cancel-dups lst))))

(defthm x-member-of-cancel-dups
  (implies (member-equal a (x-cancel-dups lst))
           (member-equal a lst))
  :hints (("Goal" :induct (x-cancel-dups lst))))

(defthm x-no-duplicatesp-of-cancel-dups
  (no-duplicatesp-equal (x-cancel-dups lst))
  :hints (("Goal" :induct (x-cancel-dups lst))))

(defthm x-subsetp-of-cancel-dups
  (subsetp-equal (x-cancel-dups lst) lst)
  :hints (("Goal" :induct (x-cancel-dups lst))))
