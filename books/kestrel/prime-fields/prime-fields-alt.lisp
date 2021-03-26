; Prime fields library (alternate formalization)
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

;; This book defines the finite field containing integers less than some
;; arbitrary prime where all operations are done modulo the prime.

(include-book "support")
(local (include-book "../number-theory/divides"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/mod"))

(in-theory (disable (:e rtl::primep)))

;;;
;;; prime
;;;

;; An arbitrary prime
(encapsulate (((prime) => *))
  (local (defun prime () 3))
  (defthm primep-of-prime
    (rtl::primep (prime))
    :hints (("Goal" :in-theory (enable rtl::primep)))))

(defthm primep-forward-to-posp
  (implies (rtl::primep x)
           (posp x))
  :rule-classes :forward-chaining)

(defthm primep-forward-to-bound
  (implies (rtl::primep x)
           (<= 2 x))
  :rule-classes :forward-chaining)

;; Since 1 is now its own type, this is a good :type-prescription rule.
(defthm prime-type
  (and (integerp (prime))
       (<= 2 (prime)))
  :rule-classes :type-prescription)

;drop?
(defthm prime-linear
  (<= 2 (prime))
  :rule-classes :linear)

;;;
;;; fep ("field element predicate")
;;;

;; Recognize an element of the field. "fep" = "field element predicate"
(defund fep (x)
  (declare (xargs :guard t))
  (and (natp x)
       (< x (prime))))

(in-theory (disable (:e fep)))

(defthm fep-fw-to-natp
  (implies (fep x)
           (natp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fep))))

(defthm fep-fw-to-bound
  (implies (fep x)
           (< x (prime)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fep))))

;; 0 is in the field
(defthm fep-of-0
  (fep 0)
  :hints (("Goal" :in-theory (enable fep))))

;; 1 is in the field
(defthm fep-of-1
  (fep 1)
  :hints (("Goal" :in-theory (enable fep))))

;; This breaks the abstraction a bit, but mod can appear when add, sub, or neg
;; is applied to constant arguments.
(defthm fep-of-mod-of-prime
  (implies (integerp x)
           (fep (mod x (prime))))
  :hints (("Goal" :in-theory (enable fep))))

;;;
;;; minus1
;;;

;; this is equal to p-1, but it can help to think of it as "negative 1"
(defund minus1 ()
  (declare (xargs :guard t))
  (+ -1 (prime)))

(in-theory (disable (:e minus1)))

;; -1 is in the field
(defthm fep-of-minus1
  (fep (minus1))
  :hints (("Goal" :in-theory (enable fep minus1))))

(defthm not-equal-of-0-and-minus1
  (not (equal 0 (minus1)))
  :hints (("Goal" :in-theory (enable fep minus1))))

(defthm natp-of-one-less-than-minus1
  (natp (+ -1 (minus1))) ;the addition here is not the field addition
  :hints (("Goal" :in-theory (enable minus1))))

;;;
;;; add
;;;

;; Compute the sum of x and y modulo the prime.
(defund add (x y)
  (declare (xargs :guard (and (fep x)
                              (fep y))))
  (mod (+ x y) (prime)))

(in-theory (disable (:e add)))

(defthm fep-of-add
  (implies (and (fep x)
                (fep y))
           (fep (add x y)))
  :hints (("Goal" :in-theory (enable add fep))))

(defthm add-of-0-arg1
  (implies (fep x)
           (equal (add 0 x)
                  x))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of-0-arg2
  (implies (fep x)
           (equal (add x 0)
                  x))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-associative
  (implies (and (fep x)
                (fep y)
                (fep z))
           (equal (add (add x y) z)
                  (add x (add y z))))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-commutative
  (implies (and (fep x)
                (fep y))
           (equal (add x y)
                  (add y x)))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-commutative-2
  (implies (and (fep x)
                (fep y)
                (fep z))
           (equal (add x (add y z))
                  (add y (add x z))))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-constant-opener
  (implies (syntaxp (and (quotep x)
                         (quotep y)))
           (equal (add x y)
                  ;; the sum here gets computed:
                  (mod (+ x y) (prime))))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-combine-constants
  (implies (and (syntaxp (and (quotep x)
                              (quotep y)))
                (fep x)
                (fep y)
                (fep z))
           (equal (add x (add y z))
                  (add (add x y) z)))
  :hints (("Goal" :in-theory (enable add))))

(defthm equal-of-add-cancel-1
  (implies (and (fep x)
                (fep y))
           (equal (equal x (add x y))
                  (equal 0 y)))
  :hints (("Goal" :in-theory (enable add acl2::mod-sum-cases))))

;;;
;;; sub
;;;

;; Compute the difference of x and y modulo the prime.
(defund sub (x y)
  (declare (xargs :guard (and (fep x)
                              (fep y))))
  (mod (- x y) (prime)))

(in-theory (disable (:e sub)))

(defthm sub-constant-opener
  (implies (syntaxp (and (quotep x)
                         (quotep y)))
           (equal (sub x y)
                  ;; the difference here gets computed:
                  (mod (- x y) (prime))))
  :hints (("Goal" :in-theory (enable sub))))

(defthm fep-of-sub
  (implies (and (fep x)
                (fep y))
           (fep (sub x y)))
  :hints (("Goal" :in-theory (enable sub fep))))

(defthm sub-of-0
  (implies (fep x)
           (equal (sub x 0)
                  x))
  :hints (("Goal" :in-theory (enable sub))))

(defthm sub-same
  (implies (fep x)
           (equal (sub x x)
                  0))
  :hints (("Goal" :in-theory (enable sub))))

(defthm sub-same-2
  (implies (and (fep x)
                (fep y))
           (equal (sub x (sub x y))
                  y))
  :hints (("Goal" :in-theory (enable sub))))

(defthm equal-of-0-and-sub
  (implies (and (fep x)
                (fep y))
           (equal (equal 0 (sub x y))
                  (equal x y)))
  :hints (("Goal" :in-theory (enable sub fep acl2::mod-sum-cases))))

(defthm equal-of-sub-and-sub-cancel-1
  (implies (and (fep x)
                (fep y)
                (fep z))
           (equal (equal (sub x y) (sub x z))
                  (equal y z)))
  :hints (("Goal" :in-theory (enable sub))))

(defthm equal-of-sub-combine-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (fep x)
                (fep k1)
                (fep k2))
           (equal (equal k1 (sub k2 x))
                  (equal x (sub k2 k1))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable sub))))

;;;
;;; neg
;;;

;; Compute the (unary) negation of x modulo the prime.
(defund neg (x)
  (declare (xargs :guard (fep x)))
  (sub 0 x))

(defthm neg-constant-opener
  (implies (and (syntaxp (quotep x))
                (fep x))
           (equal (neg x)
                  ;; the negation here gets computed:
                  (mod (- x) (prime))))
  :hints (("Goal" :in-theory (enable neg sub))))

(in-theory (disable (:e neg)))

(defthm fep-of-neg
  (implies (fep x)
           (fep (neg x)))
  :hints (("Goal" :in-theory (enable neg fep))))

(defthm equal-of-neg-solve
  (implies (and (syntaxp (quotep k1))
                (fep x)
                (fep k1))
           (equal (equal k1 (neg x))
                  (equal x (neg k1))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable neg))))

(defthm equal-of-neg-and-one-less-than-prime
  (implies (fep x)
           (equal (equal (neg x) (+ -1 (prime)))
                  (equal x 1)))
  :hints (("Goal" :in-theory (enable neg sub))))


;;;
;;; mul
;;;

;; Compute the product of x and y modulo the prime.
(defund mul (x y)
  (declare (xargs :guard (and (fep x)
                              (fep y))))
  (mod (* x y) (prime)))

(in-theory (disable (:e mul)))

(defthm fep-of-mul
  (implies (and (fep x)
                (fep y))
           (fep (mul x y)))
  :hints (("Goal" :in-theory (enable mul fep))))

(defthm mul-of-1-arg1
  (implies (fep x)
           (equal (mul 1 x)
                  x))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-1-arg2
  (implies (fep x)
           (equal (mul x 1)
                  x))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-0-arg1
  (implies (fep x)
           (equal (mul 0 x)
                  0))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-0-arg2
  (implies (fep x)
           (equal (mul x 0)
                  0))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-commutative
  (implies (and (fep x)
                (fep y))
           (equal (mul x y)
                  (mul y x)))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-associative
  (implies (and (fep x)
                (fep y)
                (fep z))
           (equal (mul (mul x y) z)
                  (mul x (mul y z))))
  :hints (("Goal" :in-theory (enable mul))))

;;;
;;; pow
;;;

;; Compute x to the nth power (x^n) modulo the prime. Note that n can be any natural.
(defund pow (x n)
  (declare (xargs :guard (and (fep x)
                              (natp n))
                  :verify-guards nil ;done below
                  ))
  (if (or (not (mbt (natp n)))
          (equal 0 n))
      1
    (mul x (pow x (+ -1 n)))))

(in-theory (disable (:e pow)))

(defthm fep-of-pow
  (implies (and (fep a)
                (natp b))
           (fep (pow a b)))
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-of-+
  (implies (and (fep a)
                (natp b)
                (natp c))
           (equal (pow a (+ b c))
                  (mul (pow a b)
                       (pow a c))))
  :hints (("Goal" :in-theory (enable pow))))

(verify-guards pow)

(defthm pow-of-0
  (implies (fep a)
           (equal (pow a 0)
                  1))
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-of-1
  (implies (fep a)
           (equal (pow a 1)
                  a))
  :hints (("Goal" :in-theory (enable pow))))

;; express pow in terms of expt and do the entire mod at the end
(defthmd pow-rewrite
  (implies (and (natp a)
                (natp b))
           (equal (pow a b)
                  (mod (expt a b) (prime))))
  :hints (("Goal" :in-theory (enable pow mul expt))))

(defthmd pow-opener
  (implies (posp n)
           (equal (pow x n)
                  (mul x (pow x (+ -1 n)))))
  :hints (("Goal" :in-theory (enable pow))))

;;;
;;; inv
;;;

;; Compute the multiplicative inverse of x modulo the prime.
;; See theorem inv-correct below.
(defund inv (x)
  (declare (xargs :guard (and (fep x)
                              (not (equal x 0)))
                  :guard-hints (("Goal" :in-theory (enable minus1)))))
  (pow x (+ -1 (minus1))))

(in-theory (disable (:e inv)))

(defthm fep-of-inv
  (implies (fep a)
           (fep (inv a)))
  :hints (("Goal" :in-theory (enable inv minus1))))

;;;
;;; div
;;;

;; Divide x by y modulo the prime.
(defund div (x y)
  (declare (xargs :guard (and (fep x)
                              (fep y)
                              (not (equal 0 y)))))
  (mul x (inv y)))

(in-theory (disable (:e div)))

(defthm fep-of-div
  (implies (and (fep x)
                (fep y))
           (fep (div x y)))
  :hints (("Goal" :in-theory (enable div))))

;;;
;;; rules
;;;

(defthm add-of-sub-arg1
  (implies (and (fep x)
                (fep y)
                (fep z))
           (equal (add (sub x y) z)
                  (add x (add z (neg y)))))
  :hints (("Goal" :in-theory (enable add sub neg))))

(defthm add-of-sub-arg2
  (implies (and (fep x)
                (fep y)
                (fep z))
           (equal (add z (sub x y))
                  (add x (add z (neg y)))))
  :hints (("Goal" :in-theory (enable add sub neg))))

(defthmd sub-opener
  (implies (and (fep x)
                (fep y))
           (equal (sub x y)
                  (add x (neg y))))
  :hints (("Goal" :in-theory (enable add sub neg))))

(defthmd equal-of-0-and-add
  (implies (and (fep x)
                (fep y))
           (equal (equal 0 (add y x))
                  (equal x (sub 0 y))))
  :hints (("Goal" :in-theory (enable add sub acl2::mod-sum-cases))))

(defthm equal-of-0-and-add-safe
  (implies (and (syntaxp (quotep y))
                (fep x)
                (fep y))
           (equal (equal 0 (add y x))
                  (equal x (sub 0 y))))
  :hints (("Goal" :in-theory (enable equal-of-0-and-add))))

(defthm equal-of-add-combine-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (fep x)
                (fep k1)
                (fep k2))
           (equal (equal k1 (add k2 x))
                  (equal x (sub k1 k2))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable sub add))))

;; (defthm pow-of-+-of-1
;;   (implies (and (fep a)
;;                 (natp b))
;;            (equal (pow a (+ 1 b))
;;                   (mul a (pow a b))))
;;   :hints (("Goal" :in-theory (enable pow))))

;move?
(defthm divides-of-prime-means-0
  (implies (fep x)
           (equal (rtl::divides (prime) x)
                  (equal 0 x)))
  :hints (("Goal" :in-theory (enable fep))))

;move?
(defthm equal-of-0-and-mul
  (implies (and (fep x)
                (fep y))
           (equal (equal 0 (mul x y))
                  (or (equal x 0)
                      (equal y 0))))
  :hints (("Goal"
           :use (primep-of-prime
                 (:instance rtl::euclid
                            (p (prime))
                            (a x)
                            (b y)))
           :in-theory (enable mul
                              acl2::equal-of-0-and-mod
                              rtl::divides))))

;;Obtain an instance of Fermat's little theorem for the prime (prime).
(encapsulate
  ()
  (local (include-book "../../projects/quadratic-reciprocity/fermat"))
  (local (include-book "../../arithmetic-3/top"))

  (defthm my-fermat-little
    (implies (and (fep a)
                  (not (equal 0 a)))
             (equal (pow a (minus1))
                    1))
    :hints (("Goal" :use (primep-of-prime
                          (:instance rtl::fermat
                                     (m a)
                                     (p (prime))))
             :cases ((equal 0 a))
             :in-theory (e/d (pow-rewrite fep minus1)
                             (expt (:e expt) (:e rtl::primep)))))))

(defthm inv-correct
  (implies (and (fep a)
                (not (equal 0 a)))
           (equal (mul a (inv a))
                  1))
  :hints (("Goal" :in-theory (e/d (inv) (pow-of-+ my-fermat-little))
           :expand (pow a (minus1))
           :use (:instance my-fermat-little))))

(defthm inv-correct-alt
  (implies (and (fep a)
                (not (equal 0 a)))
           (equal (mul (inv a) a)
                  1))
  :hints (("Goal" :use (:instance inv-correct)
           :in-theory (disable inv-correct))))

;; 2 is in the field iff the prime is bigger than 2.
(defthm fep-of-2
  (equal (fep 2)
         (not (equal 2 (prime))))
  :hints (("Goal" :in-theory (enable fep))))

(defthm fep-of-prime-minus-1
  (fep (+ -1 (prime)))
  :hints (("Goal" :in-theory (enable fep))))

(defthmd sub-becomes-add-of-neg
  (implies (and (fep x)
                (fep y))
           (equal (sub x y)
                  (add x (neg y))))
  :hints (("Goal" :in-theory (enable add sub neg))))

(defthm mul-of-minus1-becomes-neg
  (implies (fep x)
           (equal (mul (minus1) x)
                  (neg x)))
  :hints (("Goal" :in-theory (enable mul neg sub minus1 fep acl2::mod-sum-cases))))
