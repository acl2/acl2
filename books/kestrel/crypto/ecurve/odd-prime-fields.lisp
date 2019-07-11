; Elliptic Curve Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Nathan Guermond (guermond@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

; for primep definition
(include-book "projects/quadratic-reciprocity/euclid" :dir :system)

; for fermat's little theorem
(include-book "projects/quadratic-reciprocity/fermat" :dir :system)

(include-book "kestrel/utilities/integer-arithmetic/top" :dir :system)

(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

; for dec-induct
(local (include-book "std/basic/inductions" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Odd Prime Fields
; ----------------

; In this book we define operations for odd prime fields,
; i.e. prime fields where the prime is odd.
; This book is independent from elliptic curves,
; but it is part of the elliptic curve library
; because it was developed for that library;
; we may factor this out into an independent library at some point,
; but before that we would probably want to generalize this to prime fields
; where the prime is not necessarily odd (i.e. include 2 as a possible prime).
; On the other hand, we have another development of (odd and even) prime fields
; that may be preferable to this one from certain points of view;
; that development may eventually supersede the one in this book.

; Our definition of the prime field Fp is as follows:
; 1. An element is any integer,
;    more precisely an equivalence class of integers modulo p.
; 2. Addition, subtraction, and multiplication are given by
;    the standard multiplication on integers,
;    more precisely i+, i-, and i* from the integer arithmetic library.
; 3. The multiplicative inverse of x is /p, defined as (expt x (- p 2)),
;    based on Fermat's Little Theorem.
; 4. We have a normalization operation modp
;    that maps any integer to its equivalence class representative.
; 5. Equality =p of elements x and y is defined as (equal (modp x) (modp y)).

; We choose to define elements of Fp as integers
; because that obviates the need to re-prove the large corpus of rules in ACL2.
; In addition, taking equivalence classes of integers also means that
; we do not have to deal with modulus and exponentiation in our reasoning,
; and their definitions can be kept essentially disabled throughout.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We introduce an arbitrary odd prime as a constrained nullary function.
; Our development of odd prime fields is parameterized over this prime.

(encapsulate
  (((prime) => *))

  (local (defun prime () 3))

  (defthm primep-of-prime
    (rtl::primep (prime))
    :hints (("Goal" :in-theory (enable rtl::primep))))

  ;; we need this because we divide (1- (prime)) by 2 later in this file
  (defthm prime-is-odd
    (> (prime) 2)
    ;; this cannot be a linear rule inside this encapsulate,
    ;; because (prime) gets evaluated to 3 when forming the linear rule
    :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A few basic properties of the prime.

(defthm posp-of-prime-type
  (posp (prime))
  :rule-classes :type-prescription
  :hints (("Goal" :use primep-of-prime :in-theory (disable primep-of-prime))))

(defthm prime-greater-than-2
  (> (prime) 2)
  :rule-classes :linear
  :hints (("Goal" :by prime-is-odd)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Normalization operation over the field.

(defund modp (x)
  (declare (xargs :guard (integerp x)))
  (mod (ifix x) (prime)))

(in-theory (disable (:e modp))) ; because it depends on non-executable PRIME

(defthm modp-type-prescription-ensure ; ensure that (:t modp) is natp
  (natp (modp x))
  :rule-classes nil
  :hints (("Goal" :in-theory '(natp (:t modp)))))

(defthm modp-of-modp
  (equal (modp (modp x)) (modp x))
  :hints (("Goal" :in-theory (enable modp))))

(defthm modp-<-prime
  (< (modp x) (prime))
  :hints (("Goal" :in-theory (enable modp))))

(defthm modp-of-0
  (equal (modp 0) 0)
  :hints (("Goal" :in-theory (enable modp))))

(defthm modp-of-1
  (equal (modp 1) 1)
  :hints (("Goal" :in-theory (enable modp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Equality over the field.

(defund =p (x y)
  (declare (xargs :guard (and (integerp x) (integerp y))))
  (equal (modp x) (modp y)))

(in-theory (disable (:e =p))) ; because it depends on non-executable PRIME

(defthm |0 p/= 1|
  (not (=p 0 1))
  :hints (("Goal" :in-theory (enable =p))))

(defthm |1 p/= 0|
  (not (=p 1 0))
  :hints (("Goal" :in-theory (enable =p))))

(defthm |2 p/= 0|
  (not (=p 2 0))
  :hints (("Goal" :in-theory (enable =p modp))))

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm |1 p/= -1|
    (not (=p 1 -1))
    :hints (("Goal" :in-theory (enable =p modp)))))

; =p is an equivalence relation
(defequiv =p
  :hints (("Goal" :in-theory (enable =p modp))))

; =p is a congruence for i+, i*, and i-
(encapsulate ()

  (local (include-book "arithmetic-5/top" :dir :system))

  ;; the following congruence rules are false
  ;; for the general arithmetic operations,
  ;; so we must restrict them to integer arithmetic

  (local (in-theory (enable i+ i* i- =p modp)))

  ;; note: congruence for division (/p) is proved later
  (defcong =p =p (i+ x y) 1)
  (defcong =p =p (i+ x y) 2)
  (defcong =p =p (i* x y) 1)
  (defcong =p =p (i* x y) 2)
  (defcong =p =p (i- x) 1))

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm prime-divides-iff-=p-0
    (implies (integerp x)
             (iff (rtl::divides (prime) x)
                  (=p x 0)))
    :hints (("Goal" :in-theory (enable =p rtl::divides modp)))))

; =p is (conditionally) a congruence for expt
; (used to prove congruence for division later)
(defthmd expt-congruence
  (implies (and (=p x x-equiv)
                (integerp x)
                (integerp x-equiv)
                (natp n))
           (=p (expt x n)
               (expt x-equiv n)))
  :hints (("Goal"
           :induct (acl2::dec-induct n)
           :in-theory (enable =p modp i*))
          ("Subgoal *1/2"
           :expand ((expt x n) (expt x-equiv n))
           :use ((:instance =p-implies-=p-i*-1 (y (expt x-equiv (1- n))))
                 (:instance =p-implies-=p-i*-2
                  (y (expt x (1- n)))
                  (y-equiv (expt x-equiv (1- n))))))))

(defthm equal-forward-to-=p
  (implies (equal x y)
           (=p x y))
  :rule-classes :forward-chaining)

(defthm =p-of-modp
  (=p (modp x) x)
  :hints (("Goal" :in-theory (enable =p))))

(defthm |=p x x|
  (=p x x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Inverse operation over the field.

(defund /p (x)
  (declare (xargs :guard (integerp x)))
  (expt (ifix x) (- (prime) 2)))

(in-theory (disable (:e /p))) ; because it depends on non-executable PRIME

(defthm integerp-of-/p
  (integerp (/p x))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable /p))))

(defthmd =p-implies-=p-/p-1-lemma ; to prove congruence for /p below
  (implies (=p x x-equiv)
           (=p (/p x)
               (/p x-equiv)))
  :hints (("Goal"
           :in-theory (enable /p =p modp)
           :use ((:instance expt-congruence (n (- (prime) 2)))
                 (:instance expt-congruence (x 0) (n (- (prime) 2)))
                 (:instance expt-congruence (x-equiv 0) (n (- (prime) 2)))))))

; =p is a congruence rule for /p
(defcong =p =p (/p x) 1
  :hints (("Goal" :by =p-implies-=p-/p-1-lemma)))

(defthm /p-identity-left
  (implies (force (not (=p x 0)))
           (=p (i* (/p x) x) 1))
  :hints (("Goal"
           :in-theory (enable =p modp /p i* expt)
           :use (:instance rtl::fermat (p (prime)) (m x)))))

(defthm /p-identity-right
  (implies (force (not (=p x 0)))
           (=p (i* x (/p x)) 1))
  :hints (("Goal"
           :in-theory (enable =p modp /p i* expt)
           :use (:instance rtl::fermat (p (prime)) (m x)))))

(defthm /p-cancellation-on-left
  (implies (force (not (=p x 0)))
           (=p (i* x (i* (/p x) y)) y))
  :hints (("Goal"
           :in-theory (disable acl2::commutativity-2-of-i* /p-identity-right)
           :use ((:instance acl2::commutativity-2-of-i*
                  (x x)
                  (y y)
                  (z (/p x)))
                 (:instance /p-identity-right)))
          ("Subgoal 1" :in-theory (enable =p modp))))

(defthm /p-cancellation-on-right
  (implies (force (not (=p x 0)))
           (=p (i* x (i* y (/p x))) y))
  :hints (("Goal"
           :in-theory (disable acl2::commutativity-2-of-i* /p-identity-right)
           :use ((:instance acl2::commutativity-2-of-i*
                  (x x)
                  (y y)
                  (z (/p x)))
                 (:instance /p-identity-right)))
          ("Subgoal 1" :in-theory (enable =p modp))))

(defthm /p-cancellation-3 ; this could be generalized into a meta rule
  (implies (force (not (=p x 0)))
           (=p (i* x y (/p x) z)
               (i* y z)))
  :hints (("Goal"
           :in-theory (disable acl2::commutativity-2-of-i*)
           :use ((:instance acl2::commutativity-2-of-i*
                  (x x)
                  (y y)
                  (z (i* (/p x) z)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some properties of field multiplication and division.

(defthmd |x * y =p 0 --> x =p 0 or y =p 0|
  (implies (=p (i* x y) 0)
           (or (=p x 0)
               (=p y 0)))
  :hints (("Goal"
           :cases ((=p x 0))
           :in-theory (disable =p-implies-=p-i*-2)
           :use (:instance =p-implies-=p-i*-2
                 (x (/p x))
                 (y (i* x y))
                 (y-equiv 0)))))

(defthm |x * x =p 0 --> x =p 0|
  (implies (=p (i* x x) 0)
           (=p x 0))
  :hints (("Goal" :use (:instance |x * y =p 0 --> x =p 0 or y =p 0|
                        (y x))))
  :rule-classes ((:forward-chaining :trigger-terms ((=p (i* x x) 0)))))

(encapsulate ()
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (defthm distributivity-of-/p-over-i*
    (=p (/p (i* x y))
        (i* (/p x) (/p y)))
    :hints (("Goal" :in-theory (enable i* =p /p)))))

(encapsulate ()
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (defthmd *-of-/p-2
    (implies (integerp (/ n 2))
             (=p (* n (/p 2)) (/ n 2)))
    :hints (("Goal"
             :cases ((equal n (* (/ n 2) 2)))
             :in-theory (e/d (i*) (commutativity-of-*)))
            ("Subgoal 1"
             :in-theory (e/d (i*)
                             (/p-cancellation-on-left
                              /p-identity-right commutativity-of-*))
             :use ((:instance /p-identity-right
                    (x 2))
                   (:instance =p-implies-=p-i*-2
                    (x (* n 1/2))
                    (y (* 2 (/p 2)))
                    (y-equiv 1))))
            ("Subgoal 1.3"
             :in-theory (enable i*)
             :use (:instance integerp-of-/p (x 2))
             :expand (/p 2))
            ("Subgoal 1.1"
             :in-theory (enable i*)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some properties of field addition and subtraction.

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm =p-of-i+-and-i+-cancel
    (equal (=p (i+ x y) (i+ x z))
           (=p y z))
    :hints (("Goal" :do-not '(preprocess) :in-theory (enable =p modp i+)))))

(defthm |x =p -x --> x =p 0|
  (implies (=p x (i- x))
           (=p x 0))
  :hints (("Goal" :use ((:instance =p-implies-=p-i*-1
                         (x x)
                         (x-equiv (i- x))
                         (y (/p x))))))
  :rule-classes ((:forward-chaining :trigger-terms ((=p x (i- x))))))

(defthm |x =p -y --> x + y =p 0|
  (implies (=p x (i- y))
           (=p (i+ x y) 0))
  :hints (("Goal"
           :in-theory (disable acl2::cancel_iplus-equal-correct
                               =p-implies-=p-i+-1
                               =p-implies-=p-i+-2)
           :use (:instance =p-implies-=p-i+-1
                 (x-equiv (i- y))))))

(defthmd |x - y =p 0 --> x =p y|
  (implies (=p (i- x y) 0)
           (=p x y))
  :hints (("Goal"
           :in-theory (enable =p modp)
           :use ((:instance =p-implies-=p-i+-1
                  (x (i- x y))
                  (x-equiv 0)
                  (y y))))))

(defthm |x + x =p 0 --> x =p 0|
  (implies (=p (i+ x x) 0)
           (=p x 0))
  :hints (("Goal"
           :in-theory (enable =p modp)
           :use ((:instance =p-implies-=p-i+-1
                  (x (i+ x x)) (x-equiv 0) (y (i- x)))
                 (:instance |x =p -x --> x =p 0|)))))

(defthmd |-x =p -y --> x =p y|
  (implies (=p (i- x) (i- y))
           (=p x y))
  :hints (("Goal"
           :in-theory (e/d (=p modp)
                           (=p-implies-=p-i+-1 =p-implies-=p-i+-2))
           :use (:instance =p-implies-=p-i+-1
                 (x (i- x))
                 (x-equiv (i- y))
                 (y (i+ x y))))))

(defthmd |x + y =p 0 & x - y =p 0 --> x =p 0 & y =p 0|
  (implies (and (=p (i+ x y) 0)
                (=p (i- x y) 0))
           (and (=p x 0)
                (=p y 0)))
  :hints (("Goal"
           :in-theory (disable |x =p -x --> x =p 0|)
           :use (|x - y =p 0 --> x =p y|
                 |x + x =p 0 --> x =p 0|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Other properties of the field operations.

(defthmd |x^2 =p y^2 --> x =p y or x =p -y|
  (implies (and (integerp y)
                (=p (i* x x) (i* y y)))
           (or (=p x y)
               (=p x (i- y))))
  :hints (("Goal"
           :use ((:instance |x * y =p 0 --> x =p 0 or y =p 0|
                  (x (i- x y))
                  (y (i+ x y)))
                 (:instance |x - y =p 0 --> x =p y|
                  (y (i- y)))
                 (:instance |x - y =p 0 --> x =p y|)))))

(defthmd |x^2 =p 1 --> x =p 1 or x =p -1|
  (implies (=p (i* x x) 1)
           (or (=p x 1)
               (=p x (i- 1))))
  :hints (("Goal" :use (:instance |x^2 =p y^2 --> x =p y or x =p -y|
                        (y 1)))))

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthmd expt-is-hom
    (implies (and (integerp x)
                  (natp n))
             (equal (expt (i* x x) n)
                    (expt x (* 2 n))))
    :hints (("Goal" :in-theory (enable i*)))))

; Fermat's Little Theorem
(defthm fermat
  (implies (not (=p m 0))
           (=p (expt m (1- (prime))) 1))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable =p modp)
           :use (:instance rtl::fermat (m m) (p (prime))))))

; the whole identity is shown in "projects/quadratic-reciprocity/euler"
(defthmd weak-euler-criterion
  (implies (and (integerp sqrt{a})
                (integerp a)
                (not (=p a 0))
                (=p a (i* sqrt{a} sqrt{a})))
           (=p (expt a (/ (- (prime) 1) 2)) 1))
  :hints (("Goal" :use ((:instance expt-congruence
                         (x a)
                         (x-equiv (i* sqrt{a} sqrt{a}))
                         (n (/ (- (prime) 1) 2)))
                        (:instance expt-is-hom
                         (x sqrt{a})
                         (n (/ (- (prime) 1) 2)))
                        (:instance fermat
                                   (m sqrt{a})))
           :in-theory (enable expt))))
