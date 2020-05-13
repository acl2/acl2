; Prime fields library
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

;; This book defines operations on the finite field consisting of the integers
;; modulo some prime p.

;; The rules in the book generally each deal with a single function. For
;; reasoning about these operations, consider including the book
;; prime-fields-rules.

;; In this version of the formalization, the prime is passed explicitly to all
;; of the operations.  See also prime-fields-alt.lisp, which uses a constrained
;; function for the prime.

(include-book "../../arithmetic-3/floor-mod/mod-expt-fast") ;just provides mod-expt-fast
(include-book "support")
(include-book "../utilities/smaller-termp")
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/mod"))

(in-theory (disable (:e rtl::primep)))

(defmacro primep (x) `(rtl::primep ,x))

;;;
;;; prime
;;;

(defthm primep-forward-to-posp
  (implies (primep x)
           (posp x))
  :rule-classes :forward-chaining)

(defthm primep-forward-to-bound
  (implies (primep x)
           (<= 2 x))
  :rule-classes :forward-chaining)

;;;
;;; fep ("field element predicate")
;;;

;; Recognize an element of the field. "fep" = "field element predicate"
(defund fep (x p)
  (declare (xargs :guard (integerp p)))
  (and (natp x)
       (< x p)))

(defthm fep-fw-to-natp
  (implies (fep x p)
           (natp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fep))))

(defthm fep-fw-to-bound
  (implies (fep x p)
           (< x p))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fep))))

;; 0 is in the field
(defthm fep-of-0
  (implies (posp p)
           (fep 0 p))
  :hints (("Goal" :in-theory (enable fep))))

;; 1 is in the field
(defthm fep-of-1
  (implies (and (integerp p)
                (< 1 p))
           (fep 1 p))
  :hints (("Goal" :in-theory (enable fep))))

;; This breaks the abstraction a bit, but mod can appear when add, sub, or neg
;; is applied to constant arguments.
(defthm fep-of-mod
  (implies (and (integerp x)
                (posp p))
           (fep (mod x p) p))
  :hints (("Goal" :in-theory (enable fep))))

;;;
;;; minus1
;;;

;; this is equal to p-1, but it can help to think of it as "negative 1"
(defund minus1 (p)
  (declare (xargs :guard (integerp p)))
  (+ -1 p))

(defthm integerp-of-minus1
  (implies (integerp p)
           (integerp (minus1 p)))
  :hints (("Goal" :in-theory (enable fep minus1))))

;; -1 is in the field
(defthm fep-of-minus1
  (implies (posp p)
           (fep (minus1 p) p))
  :hints (("Goal" :in-theory (enable fep minus1))))

(defthm not-equal-of-0-and-minus1
  (implies (< 1 p)
           (not (equal 0 (minus1 p))))
  :hints (("Goal" :in-theory (enable fep minus1))))

(defthm natp-of-one-less-than-minus1
  (implies (and (integerp p)
                (< 1 p))
           (natp (+ -1 (minus1 p))) ;the addition here is not the field addition
           )
  :hints (("Goal" :in-theory (enable minus1))))

;;;
;;; add
;;;

;; Compute the sum of x and y modulo the prime.
(defund add (x y p)
  (declare (xargs :guard (and (integerp p)
                              (fep x p)
                              (fep y p))))
  (mod (+ x y) p))

(defthm integerp-of-add
  (implies (and (integerp x)
                (integerp y)
                (integerp p))
           (integerp (add x y p)))
  :hints (("Goal" :in-theory (enable fep add))))

(defthm natp-of-add
  (implies (and (natp x)
                (natp y)
                (posp p))
           (natp (add x y p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fep add))))

(defthm fep-of-add
  (implies (and (fep x p)
                (fep y p)
                (integerp p))
           (fep (add x y p) p))
  :hints (("Goal" :in-theory (enable add fep))))

(defthm rationalp-of-add
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (add x y p)))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of-0-arg1
  (implies (and (fep x p)
                (integerp p))
           (equal (add 0 x p)
                  x))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of-0-arg2
  (implies (and (fep x p)
                (integerp p))
           (equal (add x 0 p)
                  x))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-associative
  (implies (and (integerp x) ;(fep x p)
                (integerp y) ;(fep y p)
                (integerp z) ;(fep z p)
                (posp p))
           (equal (add (add x y p) z p)
                  (add x (add y z p) p)))
  :hints (("Goal" :in-theory (enable add))))

(defun strip-neg (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (consp x)
           (eq 'neg (ffn-symb x)))
      (cadr x)
    x))

(defun strip-constant-mul (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (consp x)
           (eq 'mul (ffn-symb x))
           (quotep (cadr x))
           )
      (caddr x)
    x))

;; compare terms ignoring calls to inv
(defun smaller-add-termp (x y)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (smaller-termp (strip-constant-mul (strip-neg x))
                 (strip-constant-mul (strip-neg y))))

(defthm add-commutative
  (implies (and (syntaxp (smaller-add-termp y x))
                (integerp x) ;(fep x p)
                (integerp y) ;(fep y p)
                )
           (equal (add x y p)
                  (add y x p)))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-commutative-2
  (implies (and (syntaxp (smaller-add-termp y x))
                (integerp x) ;(fep x p)
                (integerp y) ;(fep y p)
                (integerp z) ;(fep z p)
                (posp p)
                )
           (equal (add x (add y z p) p)
                  (add y (add x z p) p)))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-combine-constants
  (implies (and (syntaxp (and (quotep x)
                              (quotep y)))
                (fep x p)
                (fep y p)
                (fep z p)
                (integerp p))
           (equal (add x (add y z p) p)
                  (add (add x y p) z p)))
  :hints (("Goal" :in-theory (enable add))))

(defthm equal-of-add-cancel-1
  (implies (and (fep x p)
                (fep y p)
                (integerp p))
           (equal (equal x (add x y p))
                  (equal 0 y)))
  :hints (("Goal" :in-theory (enable add))))

;;;
;;; neg
;;;

;; Compute the (unary) negation of x modulo the prime.
(defund neg (x p)
  (declare (xargs :guard (and (integerp p)
                              (fep x p))))
  (mod (- x) p))

(defthm integerp-of-neg
  (implies (and (integerp x)
                (integerp p))
           (integerp (neg x p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fep neg))))

(defthm natp-of-neg
  (implies (and (natp x)
                (posp p))
           (natp (neg x p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fep neg))))

(defthm neg-constant-opener
  (implies (and (syntaxp (quotep x))
                (fep x p)
                (integerp p))
           (equal (neg x p)
                  ;; the negation here gets computed:
                  (mod (- x) p)))
  :hints (("Goal" :in-theory (enable neg))))

(defthm fep-of-neg
  (implies (and (fep x p)
                (integerp p))
           (fep (neg x p) p))
  :hints (("Goal" :in-theory (enable neg fep))))

(defthm neg-of-0
  (equal (neg 0 p)
         0)
  :hints (("Goal" :in-theory (enable neg))))

(defthm equal-of-neg-solve
  (implies (and (syntaxp (and (quotep k1)
                              ;; prevent loops when both are constants:
                              (not (quotep x))))
                (fep x p)
                (fep k1 p)
                (integerp p))
           (equal (equal k1 (neg x p))
                  (equal x (neg k1 p))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable neg))))

(defthm equal-of-neg-and-one-less-than-prime
  (implies (and (fep x p)
                (< 1 p)
                (integerp p))
           (equal (equal (neg x p) (+ -1 p))
                  (equal x 1)))
  :hints (("Goal" :in-theory (enable neg))))

;;;
;;; sub
;;;

;; Compute the difference of x and y modulo the prime.  We'll usually leave sub
;; enabled, so our normal form has no calls of sub, just add and neg.
(defun sub (x y p)
  (declare (xargs :guard (and (integerp p)
                              (fep x p)
                              (fep y p))))
  (add x (neg y p) p))

(defthm integerp-of-sub
  (implies (and (integerp x)
                (integerp y)
                (integerp p))
           (integerp (sub x y p)))
  :hints (("Goal" :in-theory (enable fep sub))))

(defthm natp-of-sub
  (implies (and (natp x)
                (natp y)
                (posp p))
           (natp (sub x y p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fep sub))))

(defthm fep-of-sub
  (implies (and (fep x p)
                (fep y p)
                (integerp p))
           (fep (sub x y p) p))
  :hints (("Goal" :in-theory (enable sub fep))))

(defthm sub-of-0
  (implies (and (fep x p)
                (integerp p))
           (equal (sub x 0 p)
                  x))
  :hints (("Goal" :in-theory (enable sub))))

(defthm sub-same
  (implies (fep x p)
           (equal (sub x x p)
                  0))
  :hints (("Goal" :in-theory (enable sub neg add))))

(defthm sub-same-2
  (implies (and (fep x p)
                (fep y p)
                (integerp p))
           (equal (sub x (sub x y p) p)
                  y))
  :hints (("Goal" :in-theory (enable sub neg add))))

(defthm equal-of-0-and-sub
  (implies (and (fep x p)
                (fep y p)
                (integerp p))
           (equal (equal 0 (sub x y p))
                  (equal x y)))
  :hints (("Goal" :in-theory (enable sub add neg))))

(defthm equal-of-sub-and-sub-cancel-1
  (implies (and (fep x p)
                (fep y p)
                (fep z p)
                (integerp p))
           (equal (equal (sub x y p) (sub x z p))
                  (equal y z)))
  :hints (("Goal" :in-theory (enable sub add neg))))

(defthm equal-of-sub-combine-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (fep x p)
                (fep k1 p)
                (fep k2 p)
                (integerp p))
           (equal (equal k1 (sub k2 x p))
                  (equal x (sub k2 k1 p))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable sub add neg))))

;;;
;;; mul
;;;

;; Compute the product of x and y modulo the prime.
(defund mul (x y p)
  (declare (xargs :guard (and (integerp p)
                              (fep x p)
                              (fep y p))))
  (mod (* x y) p))

(defthm integerp-of-mul
  (implies (and (integerp x)
                (integerp y)
                (integerp p))
           (integerp (mul x y p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable mul))))

(defthm natp-of-mul
  (implies (and (natp x)
                (natp y)
                (posp p))
           (natp (mul x y p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fep mul))))

(defthm fep-of-mul
  (implies (and (fep x p)
                (fep y p)
                (integerp p))
           (fep (mul x y p) p))
  :hints (("Goal" :in-theory (enable mul fep))))

(defthm rationalp-of-mul
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (mul x y p)))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-1-arg1
  (implies (and (fep x p)
                (integerp p))
           (equal (mul 1 x p)
                  x))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-1-arg2
  (implies (and (fep x p)
                (integerp p))
           (equal (mul x 1 p)
                  x))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-0-arg1
  (implies (and (integerp x) ;(fep x p)
                (integerp p))
           (equal (mul 0 x p)
                  0))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-0-arg2
  (implies (and (integerp x) ;(fep x p)
                (integerp p))
           (equal (mul x 0 p)
                  0))
  :hints (("Goal" :in-theory (enable mul))))

(defun strip-inv (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (consp x)
           (eq 'inv (ffn-symb x)))
      (cadr x)
    x))

;; compare terms ignoring calls to inv
(defun smaller-mul-termp (x y)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (smaller-termp (strip-inv x)
                 (strip-inv y)))

(defthm mul-commutative
  (implies (and (syntaxp (smaller-mul-termp y x))
                (integerp x) ;(fep x p)
                (integerp y) ;(fep y p)
                )
           (equal (mul x y p)
                  (mul y x p)))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-commutative-2
  (implies (and (syntaxp (smaller-mul-termp y x))
                (integerp x) ;(fep x p)
                (integerp y) ;(fep y p)
                (integerp z) ;(fep z p)
                (integerp p))
           (equal (mul x (mul y z p) p)
                  (mul y (mul x z p) p)))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-associative
  (implies (and (integerp x) ;(fep x p)
                (integerp y) ;(fep y p)
                (integerp z) ;(fep z p)
                (integerp p))
           (equal (mul (mul x y p) z p)
                  (mul x (mul y z p) p)))
  :hints (("Goal" :in-theory (enable mul))))

;;;
;;; pow
;;;

;; Compute x to the nth power (x^n) modulo the prime. Note that n can be any natural.
(defund pow (x n p)
  (declare (xargs :guard (and (integerp p)
                              (< 1 p)
                              (fep x p)
                              (natp n))
                  :verify-guards nil ;done below
                  ))
  (mbe :logic (if (or (not (mbt (natp n)))
                      (equal 0 n))
                  1
                (mul x (pow x (+ -1 n) p) p))
       :exec (mod-expt-fast x n p)))

(defthm integerp-of-pow
  (implies (and (integerp x)
                (integerp p))
           (integerp (pow x n p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable pow))))

(defthm natp-of-pow
  (implies (and (natp x)
                (posp p))
           (natp (pow x n p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable pow))))

(defthm fep-of-pow
  (implies (and (fep a p)
                (natp b)
                (< 1 p)
                (integerp p))
           (fep (pow a b p) p))
  :hints (("Goal" :in-theory (enable pow))))

(defthm rationalp-of-pow
  (implies (rationalp x)
           (rationalp (pow x n p)))
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-of-+
  (implies (and (fep a p)
                (natp b)
                (natp c)
                (< 1 p)
                (integerp p))
           (equal (pow a (+ b c) p)
                  (mul (pow a b p)
                       (pow a c p)
                       p)))
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-of-0
  (implies (fep a p)
           (equal (pow a 0 p)
                  1))
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-of-1
  (implies (and (fep a p)
                (integerp p))
           (equal (pow a 1 p)
                  a))
  :hints (("Goal" :in-theory (enable pow))))

;; express pow in terms of expt and do the entire mod at the end
(defthmd pow-rewrite
  (implies (and (integerp a)
                (natp b)
                (integerp p)
                (< 1 p))
           (equal (pow a b p)
                  (mod (expt a b) p)))
  :hints (("Goal" :in-theory (enable pow mul expt))))

(verify-guards pow :hints (("Goal" :expand (EXPT X N)
                            :in-theory (enable pow-rewrite mul))))

(defthmd pow-opener
  (implies (posp n)
           (equal (pow x n p)
                  (mul x
                       (pow x (+ -1 n) p)
                       p)))
  :hints (("Goal" :in-theory (enable pow))))

;;;
;;; inv
;;;

;; Compute the multiplicative inverse of x modulo the prime.
;; See theorem inv-correct below.
(defund inv (x p)
  (declare (xargs :guard (and (integerp p)
                              (fep x p)
                              (not (equal x 0)))
                  :guard-hints (("Goal" :in-theory (enable minus1)))))
  (pow x (+ -1 (minus1 p)) p))

(defthm integerp-of-inv
  (implies (and (integerp x)
                (integerp p))
           (integerp (inv x p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable inv))))

(defthm natp-of-inv
  (implies (and (natp x)
                (posp p))
           (natp (inv x p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable inv))))

(defthm fep-of-inv
  (implies (and (fep a p)
                (< 1 p)
                (integerp p))
           (fep (inv a p) p))
  :hints (("Goal" :in-theory (enable inv minus1))))

;;;
;;; div
;;;

;; Divide x by y modulo the prime.
(defund div (x y p)
  (declare (xargs :guard (and (integerp p)
                              (fep x p)
                              (fep y p)
                              (not (equal 0 y)))))
  (mul x (inv y p) p))

(defthm integerp-of-div
  (implies (and (integerp x)
                (integerp y)
                (posp p))
           (integerp (div x y p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable div))))

(defthm natp-of-div
  (implies (and (natp x)
                (natp y)
                (posp p))
           (natp (div x y p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable div))))

(defthm fep-of-div
  (implies (and (fep x p)
                (fep y p)
                (< 1 p)
                (integerp p))
           (fep (div x y p) p))
  :hints (("Goal" :in-theory (enable div))))
