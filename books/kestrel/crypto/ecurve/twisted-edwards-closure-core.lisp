; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Nathan Guermond (guermond@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "kestrel/crypto/ecurve/odd-prime-fields" :dir :system)

(local (include-book "arithmetic/top-with-meta" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Core Closure Proof of Twisted Edwards Addition
; ----------------------------------------------

; In this book we provide a proof of
; the closure of addition for a general twisted Edwards curve,
; which has the form
;   a*x^2 + y^2 = c^2 * (1 + d*x^2*y^2)
; with the additional condition that
;   d must not be a square
;   a cannot be zero
;   a must be a square
;   c cannot be zero.

; NOTE: The requirement that 'a' must be a square is not
; required in the definition of a twisted Edwards curve,
; which makes this proof not fully general.

; This proof is derived from Theorem 3.1 and 3.3 of
;   "Faster addition and doubling on elliptic curves"
;    by Daniel Bernstein and Tanja Lange.
; Note this proof is actually for Edwards curve.
; The proof in this file is a slight generalization with additional 'a' coefficient,
; so long as 'a' is a square.

; Addition of points (x1,y1), (x2,y2) for a twisted Edwards curve
; is defined as follows:
; x3 = (x1 * y2 + y1 * x2) / (c * (1 + d * x1 * x2 * y1 * y2))
; y3 = (y1 * y2 - a * x1 * x2) / (c * (1 - d * x1 * x2 * y1 * y2))
; Note how y3 depends on 'a'.

; The main theorem in this book is that if
;   (x1,y1), (x2,y2) lie on the curve,
;   a is nonzero
;   a has a(n) (integer) square root b
;   c is nonzero
;   d is not a square
; then
;   (x3,y3) as defined above lies on the curve.

; In order to prove the closure, we also prove that
; the denominators of x3 and y3 are not 0.

; This file is meant to be included only locally in larger developments
; (or non-locally in a file that is included locally):
; the names of functions, macros, and theorems are too generic.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Square an integer.

(defmacro sq (x)
  `(i* ,x ,x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check if something is not a square in the prime field.

(defun-sk non-square (x)
  (forall n (implies (integerp n)
                     (not (=p (sq n) x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Components of the definition of x3 and y3, as functions.

(defund delta-x (x1 x2 y1 y2)
  (i+ (i* x1 y2) (i* y1 x2)))

(defund delta-y (x1 x2 y1 y2 a)
  (i- (i* y1 y2) (i* a x1 x2)))

(defund gamma (x1 x2 y1 y2 d)
  (i* d x1 y1 x2 y2))

(defund gamma+ (x1 x2 y1 y2 d)
  (i+ 1 (gamma x1 x2 y1 y2 d)))

(defund gamma- (x1 x2 y1 y2 d)
  (i- 1 (gamma x1 x2 y1 y2 d)))

(defund x3 (x1 x2 y1 y2 c d)
  (i* (delta-x x1 x2 y1 y2)
      (/p (i* c (gamma+ x1 x2 y1 y2 d)))))

(defund y3 (x1 x2 y1 y2 a c d)
  (i* (delta-y x1 x2 y1 y2 a)
      (/p (i* c (gamma- x1 x2 y1 y2 d)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Components of the curve equation, as functions.

(defund LHS (x y a)
  (i+ (i* a (sq x)) (sq y)))

(defund RHS (x y d)
  (i+ 1 (i* d (sq x) (sq y))))

(defund ECp (x y a c d)
  (=p (LHS x y a)
      (i* (sq c) (RHS x y d))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two congruence rules for ECp.
; Not needed in this file, but in other files that include this one.

(defcong =p iff (ECp x y a c d) 1
  :hints (("Goal" :in-theory (enable ECp LHS RHS))))

(defcong =p iff (ECp x y a c d) 2
  :hints (("Goal" :in-theory (enable ECp LHS RHS))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Abbreviations for the components of the definition of x3 and y3,
; with the common parameters.

(defmacro delta-x$ ()
  `(delta-x x1 x2 y1 y2))

(defmacro delta-y$ ()
  `(delta-y x1 x2 y1 y2 a))

(defmacro gamma$ ()
  `(gamma x1 x2 y1 y2 d))

(defmacro gamma+$ ()
  `(gamma+ x1 x2 y1 y2 d))

(defmacro gamma-$ ()
  `(gamma- x1 x2 y1 y2 d))

(defmacro x3$ ()
  `(x3 x1 x2 y1 y2 c d))

(defmacro y3$ ()
  `(y3 x1 x2 y1 y2 a c d))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Abbreviation for common hypotheses on
; the two points' coordinates and the curve coefficients.

(defmacro domain ()
  `(and (integerp x1)
        (integerp x2)
        (integerp y1)
        (integerp y2)
        (integerp a)
        (integerp c)
        (integerp d)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; As in the Bernstein-Lange proof, define
;   T = (x1 * y2 + x2 * y1)^2 * (1 - gamma)^2
;     + (y1 * y2 - a * x1 * x2)^2 * (1 + gamma)
;     - d * (x1 * y2 + x2 * y1)^2 * (y1 * y2 - a * x1 * x2)^2
; where
;   gamma = d * x1 * y1 * x2 * y2.

(defund TT (x1 x2 y1 y2 a d)
  (i+ (i* a (sq (delta-x$)) (sq (gamma-$)))
      (i* (sq (delta-y$)) (sq (gamma+$)))
      (i- (i* d (sq (delta-x$)) (sq (delta-y$))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Part I:
; Show that assuming gamma is not 1 or -1, (x1,y1), (x2,y2) lie on the curve,
; then appropriately defined (x3,y3) also lies on the curve.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 1

; Show that
;   T = ((LHS x1 y1) - (LHS x2 y2) * d * x1^2 * y1^2)
;     * ((LHS x2 y2) - (LHS x1 y1) * d * x2^2 * y2^2)
; where
;   (LHS x y) = a * x^2 + y^2

(defthmd reduce-TT
  (implies (domain)
           (equal (TT x1 x2 y1 y2 a d)
                  (i* (i- (LHS x1 y1 a) (i* (LHS x2 y2 a) d (sq x1) (sq y1)))
                      (i- (LHS x2 y2 a) (i* (LHS x1 y1 a) d (sq x2) (sq y2))))))
  :hints (("Goal"
           :in-theory (e/d (RHS LHS TT delta-x delta-y gamma gamma+ gamma-) ()))
          ("Goal''"
           :in-theory (enable i+ i* i-))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 2

; Now with
;   x3 = (x1 * y2 + x2 * y1) / (c * (1 + gamma))
;   y3 = (y1 * y2 - a * x1 * x2) / (c * (1 - gamma))
; we compute
;   (a * x3^2 + y3^2) - (c^2 * d * x3^2 * y3^2)
;      = T / (c^2 * (1 + gamma)^2 * (1 - gamma)^2)
; assuming gamma =/= 1,-1.

(defthmd step2
  (implies (and (domain)
                (not (=p (gamma-$) 0))
                (not (=p (gamma+$) 0))
                (not (=p c 0)))
           (=p (i- (LHS (x3$) (y3$) a) (i* (sq c) d (sq (x3$)) (sq (y3$))))
               (i* (TT x1 x2 y1 y2 a d)
                   (/p (i* (sq c) (sq (gamma+$)) (sq (gamma-$)))))))
  :hints (("Goal" :in-theory (enable LHS RHS TT x3 y3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 3

; Show that assuming (x1,y1), (x2,y2) lie on the curve,
; then T can again be rewritten:
;   T = (c^4 * (1 - gamma)^2 * (1 + gamma)^2)

(defthmd step3
  (implies (and (domain)
                (ECp x1 y1 a c d)
                (ECp x2 y2 a c d))
           ;; Note this is the same as T
           (=p (i* (i- (LHS x1 y1 a) (i* (LHS x2 y2 a) d (sq x1) (sq y1)))
                   (i- (LHS x2 y2 a) (i* (LHS x1 y1 a) d (sq x2) (sq y2))))
               (i* (sq c) (sq c) (sq (gamma-$)) (sq (gamma+$)))))
  :hints (("Goal" :in-theory (enable RHS ECp gamma- gamma+ gamma))
          ("Goal'8'" :in-theory (enable i+ i* i-))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 4

; Chain the equalities
; T = ((LHS x1 y1) - (LHS x2 y2) * d * x1^2 * y1^2) *
;       ((LHS x2 y2) - (LHS x1 y1) * d * x2^2 * y2^2)
;   = (c^2 * (1 - gamma)^2 * (1 + gamma)^2)

(defthmd step4
  (implies (and (domain)
                (ECp x1 y1 a c d)
                (ECp x2 y2 a c d))
           (=p (TT x1 x2 y1 y2 a d)
               (i* (sq c) (sq c) (sq (gamma-$)) (sq (gamma+$)))))
  :hints (("Goal" :use (step3 reduce-TT))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 5:

; We can now conclude
; (a * x3^2 + y3^2) - (c^2 * d * x3^2 * y3^2)
;   = T / (c^4 * (1 + gamma)^2 * (1 - gamma)^2)
;   = c^2

(defthmd step5
  (implies (and (domain)
                (ECp x1 y1 a c d)
                (ECp x2 y2 a c d)
                (not (=p (gamma-$) 0))
                (not (=p (gamma+$) 0))
                (not (=p c 0)))
           (=p (i- (LHS (x3$) (y3$) a) (i* (sq c) d (sq (x3$)) (sq (y3$))))
               (sq c)))
  :hints (("Goal" :use (step4 step2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 6:

; Finally we can show that
; (x3,y3) defined above lies on the curve.
; Note that we are still assuming that gamma is not 1 or -1.

(defthmd step6
  (implies (and (domain)
                (ECp x1 y1 a c d)
                (ECp x2 y2 a c d)
                (not (=p (gamma-$) 0))
                (not (=p (gamma+$) 0))
                (not (=p c 0)))
           (ECp (x3$) (y3$) a c d))
  :hints (("Goal" :in-theory (enable ECp RHS)
           :use step5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Part II:
; Show that gamma cannot be 1 or -1.
; In particular we show that gamma^2 =/= 1.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: merge the positive and negative cases

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 7:

; We first show that following identity that
;   a * x1^2 + y1^2 = d * x1^2 * y1^2 * (a * x2^2 + y2^2)
; assuming that (x1,y1), (x2,y2) lie on the curve.

(defthmd step7
  (implies (and (domain)
                (=p (sq (gamma$)) 1)
                (ECp x1 y1 a c d)
                (ECp x2 y2 a c d))
           (=p (LHS x1 y1 a)
               (i* d (sq x1) (sq y1) (LHS x2 y2 a))))
  :hints (("Goal" :in-theory (enable ECp gamma RHS))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A computational lemma.

(local
 (defthm sqrt-i*-1
   (implies (and (integerp sqrt{a})
                 (=p (sq sqrt{a}) a))
            (=p (i* sqrt{a} sqrt{a} x)
                (i* a x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 8:

; We now show that for b = sqrt(a),
;   (b * x1 + gamma * y1)
;     = (a * x1^2 + y1^2) + 2 * (b * gamma * x1 * y1)
; a must be a square

(defthmd step8-positive
  (implies (and (domain)
                (=p (sq (gamma$)) 1)
                (ECp x1 y1 a c d)
                (ECp x2 y2 a c d)
                (integerp sqrt{a})
                (=p (sq sqrt{a}) a))
           (=p (sq (i+ (i* sqrt{a} x1) (i* (gamma$) y1)))
               (i+ (LHS x1 y1 a)
                   (i* sqrt{a} (gamma$) x1 y1)
                   (i* sqrt{a} (gamma$) x1 y1))))
  :hints (("Goal" :in-theory (enable LHS))))

; We now show that for b = sqrt(a),
;   (b * x1 - gamma * y1)
;     = (a * x1^2 + y1^2) - 2 * (b * gamma * x1 * y1)

(defthmd step8-negative
  (implies (and (domain)
                (=p (sq (gamma$)) 1)
                (ECp x1 y1 a c d)
                (ECp x2 y2 a c d)
                (integerp sqrt{a})
                (=p (sq sqrt{a}) a))
           (=p (sq (i- (i* sqrt{a} x1) (i* (gamma$) y1)))
               (i- (LHS x1 y1 a)
                   (i+ (i* sqrt{a} (gamma$) x1 y1)
                       (i* sqrt{a} (gamma$) x1 y1)))))
  :hints (("Goal" :in-theory (enable LHS))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We now define several functions for encapsulation purposes.

(defund sqrt{a}*x+y-positive (x y sqrt{a})
  (i+ (i* sqrt{a} x) y))

(defund sqrt{a}*x+y-negative (x y sqrt{a})
  (i- (i* sqrt{a} x) y))

(defund top-positive (x1 y1 x2 y2 d sqrt{a})
  (i+ (i* sqrt{a} x1) (i* (gamma$) y1)))

(defund bot-positive (x1 y1 x2 y2 sqrt{a})
  (i* x1 y1 (sqrt{a}*x+y-positive x2 y2 sqrt{a})))

(defund top-negative (x1 y1 x2 y2 d sqrt{a})
  (i- (i* sqrt{a} x1) (i* (gamma$) y1)))

(defund bot-negative (x1 y1 x2 y2 sqrt{a})
  (i* x1 y1 (sqrt{a}*x+y-negative x2 y2 sqrt{a})))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 9:

; Now show that for b = sqrt{a}
;  (b * x1 + gamma * y1)^2 = d * (x1 * y1 * (b * x2 + y2))^2

(defthmd step9-positive
  (implies (and (domain)
                (=p (sq (gamma$)) 1)
                (ECp x1 y1 a c d)
                (ECp x2 y2 a c d)
                (integerp sqrt{a})
                (=p (sq sqrt{a}) a))
           (=p (sq (top-positive x1 y1 x2 y2 d sqrt{a}))
               (i* d (sq (bot-positive x1 y1 x2 y2 sqrt{a})))))
  :hints
  (("Goal"
    :in-theory (enable gamma bot-positive top-positive sqrt{a}*x+y-positive)
    :use (step7 step8-positive)
    :expand (LHS x2 y2 a))))

; Now show that for b = sqrt{a}
;  (b * x1 - gamma * y1)^2 = d * (x1 * y1 * (b * x2 - y2))^2

(defthmd step9-negative
  (implies (and (domain)
                (=p (sq (gamma$)) 1)
                (ECp x1 y1 a c d)
                (ECp x2 y2 a c d)
                (integerp sqrt{a})
                (=p (sq sqrt{a}) a))
           (=p (sq (top-negative x1 y1 x2 y2 d sqrt{a}))
               (i* d (sq (bot-negative x1 y1 x2 y2 sqrt{a})))))
  :hints
  (("Goal"
    :in-theory (enable gamma bot-negative top-negative sqrt{a}*x+y-negative)
    :use (step7 step8-negative)
    :expand (LHS x2 y2 a))))

; Show that if gamma^2 is 1, the two addend points' coordinates all not 0.

(defthmd |gamma^2 =p 1 --> x1,x2,y1,y2 p/= 0|
  (implies (and (domain)
                (=p (sq (gamma$)) 1))
           (and (not (=p x1 0))
                (not (=p x2 0))
                (not (=p y1 0))
                (not (=p y2 0))))
  :hints (("Goal" :in-theory (enable gamma))))

; Show the intended denominator is nonzero before dividing,
; under the additional assumption that (b * x2 + y2) is nonzero

(defthmd bot-positive-non-zero
  (implies (and (domain)
                (=p (sq (gamma$)) 1)
                (integerp sqrt{a})
                (not (=p (sqrt{a}*x+y-positive x2 y2 sqrt{a}) 0))
                (=p (sq sqrt{a}) a))
           (not (=p (bot-positive x1 y1 x2 y2 sqrt{a}) 0)))
  :hints (("Goal" :in-theory (enable bot-positive)
           :use (|gamma^2 =p 1 --> x1,x2,y1,y2 p/= 0|
                 (:instance |x * y =p 0 --> x =p 0 or y =p 0|
                            (x y1)
                            (y (sqrt{a}*x+y-positive x2 y2 sqrt{a})))
                 (:instance |x * y =p 0 --> x =p 0 or y =p 0|
                            (x x1)
                            (y (i* y1 (sqrt{a}*x+y-positive x2 y2 sqrt{a}))))))))

; Show the intended denominator is nonzero before dividing,
; under the additional assumption that (b * x2 - y2) is nonzero

(defthmd bot-negative-non-zero
  (implies (and (domain)
                (=p (sq (gamma$)) 1)
                (integerp sqrt{a})
                (not (=p (sqrt{a}*x+y-negative x2 y2 sqrt{a}) 0))
                (=p (sq sqrt{a}) a))
           (not (=p (bot-negative x1 y1 x2 y2 sqrt{a}) 0)))
  :hints (("Goal" :in-theory (enable bot-negative)
           :use (|gamma^2 =p 1 --> x1,x2,y1,y2 p/= 0|
                 (:instance |x * y =p 0 --> x =p 0 or y =p 0|
                            (x y1)
                            (y (sqrt{a}*x+y-negative x2 y2 sqrt{a})))
                 (:instance |x * y =p 0 --> x =p 0 or y =p 0|
                            (x x1)
                            (y (i* y1 (sqrt{a}*x+y-negative x2 y2 sqrt{a}))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 10:

; Now divide both sides from
;  (b * x1 + gamma * y1)^2 = d * (x1 * y1 * (b * x2 + y2))^2
; to see that d is a square

(defthmd step10-positive
  (implies (and (domain)
                (=p (sq (gamma$)) 1)
                (ECp x1 y1 a c d)
                (ECp x2 y2 a c d)
                (integerp sqrt{a})
                (not (=p (sqrt{a}*x+y-positive x2 y2 sqrt{a}) 0))
                (=p (sq sqrt{a}) a))
           (=p d
               (sq (i* (top-positive x1 y1 x2 y2 d sqrt{a})
                       (/p (bot-positive x1 y1 x2 y2 sqrt{a}))))))
  :hints (("Goal" :use (step9-positive bot-positive-non-zero))))


; Now divide both sides from
;  (b * x1 - gamma * y1)^2 = d * (x1 * y1 * (b * x2 - y2))^2
; to see that d is a square

(defthmd step10-negative
  (implies (and (domain)
                (=p (sq (gamma$)) 1)
                (ECp x1 y1 a c d)
                (ECp x2 y2 a c d)
                (integerp sqrt{a})
                (not (=p (sqrt{a}*x+y-negative x2 y2 sqrt{a}) 0))
                (=p (sq sqrt{a}) a))
           (=p d
               (sq (i* (top-negative x1 y1 x2 y2 d sqrt{a})
                       (/p (bot-negative x1 y1 x2 y2 sqrt{a}))))))
  :hints (("Goal" :use (step9-negative bot-negative-non-zero))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 11:

; Now combine both cases assuming that d is not a square
; to get that both
;   (b * x2 + y2) and (b * x2 - y2) must be zero.

(defthmd step11
  (implies (and (domain)
                (=p (sq (gamma$)) 1)
                (non-square d)
                (ECp x1 y1 a c d)
                (ECp x2 y2 a c d)
                (integerp sqrt{a})
                (=p (sq sqrt{a}) a))
           (and (=p (sqrt{a}*x+y-negative x2 y2 sqrt{a}) 0)
                (=p (sqrt{a}*x+y-positive x2 y2 sqrt{a}) 0)))
  :hints (("Goal" :use (step10-positive
                        step10-negative
                        (:instance non-square-necc
                         (n (i* (top-negative x1 y1 x2 y2 d sqrt{a})
                                (/p (bot-negative x1 y1 x2 y2 sqrt{a}))))
                         (x d))
                        (:instance non-square-necc
                         (n (i* (top-positive x1 y1 x2 y2 d sqrt{a})
                                (/p (bot-positive x1 y1 x2 y2 sqrt{a}))))
                         (x d))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 12:

; Show that
;   (b * x2 + y2) =p (b * x2 - y2) =p 0
; implies that
;   x2 =p y2 =p 0.

(defthmd step12
  (implies (and (domain)
                (=p (sqrt{a}*x+y-negative x2 y2 sqrt{a}) 0)
                (=p (sqrt{a}*x+y-positive x2 y2 sqrt{a}) 0)
                (not (=p sqrt{a} 0))
                (integerp sqrt{a}))
           (and (=p x2 0)
                (=p y2 0)))
  :hints (("Goal" :in-theory (enable sqrt{a}*x+y-negative
                                     sqrt{a}*x+y-positive)
           :use ((:instance |x + y =p 0 & x - y =p 0 --> x =p 0 & y =p 0|
                  (x (i* sqrt{a} x2))
                  (y y2))
                 (:instance |x * y =p 0 --> x =p 0 or y =p 0|
                  (x sqrt{a})
                  (y x2))))))

; The fact that x2 =p y2 =p 0 contradicts
; our assumption that gamma was 1,
;  since gamma = d * x1 * x2 * y1 * y2

(defthmd gamma-not-root-of-unity
  (implies (and (domain)
                (not (=p a 0))
                (non-square d)
                (integerp sqrt{a})
                (=p (sq sqrt{a}) a)
                (ECp x1 y1 a c d)
                (ECp x2 y2 a c d))
           (not (=p (sq (gamma$)) 1)))
  :hints (("Goal" :use (step12
                        step11
                        |gamma^2 =p 1 --> x1,x2,y1,y2 p/= 0|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Part III:
; Put together Parts I and II.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Still not sure why hide keeps appearing
; (even though executable counterparts should be disabled).

(defthm i+-of-i--of-hide
  (=p (i+ x (i+ (i- (hide x)) y))
      (ifix y))
  :hints (("Goal" :expand (hide x))))

(defthm sq-of-hide-1
  (=p (sq (hide 1))
      1)
  :hints (("Goal" :expand (hide 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the main closure theorem,
; which makes use of step6 from Part I
; and gamma-not-root-of-unity from Part II.

(defthmd main-theorem
  (implies (and (domain)
                (ECp x1 y1 a c d)
                (ECp x2 y2 a c d)
                (not (=p a 0))
                (non-square d)
                (=p (sq sqrt{a}) a)
                (integerp sqrt{a})
                (not (=p c 0)))
           (ECp (x3$) (y3$) a c d))
  :hints (("Goal" :in-theory (e/d (gamma- gamma+)())
           :use (step6
                 gamma-not-root-of-unity
                 (:instance =p-implies-=p-i+-1
                  (x (i- 1 (gamma$)))
                  (x-equiv 0)
                  (y (gamma$)))
                 (:instance =p-implies-=p-i+-1
                  (x (i+ 1 (gamma$)))
                  (x-equiv 0)
                  (y (i- (hide 1))))))))
