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

(include-book "kestrel/crypto/ecurve/odd-prime-fields" :dir :system)

(local (include-book "kestrel/arithmetic-light/times" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Elliptic Curve Addition Closure Lemma
; -------------------------------------

; In this book we prove the main lemma needed to prove that elliptic curve
; addition (defined in the file short-weierstrass.lisp) is closed.  Our proof
; is based on the method described in pages 169-170 of Neal Koblitz's "A Course
; in Number Theory and Cryptography", 1994, 2nd Edition.

; We choose to represent polynomials as ACL2 functions in which all
; indeterminates and free variables are treated as function parameters. For
; example, P(X) = A*X^2 + B*X + C would be defined as
;   (defun P[X] (A B C X) (i+ (i* A (i* X X)) (i* B X) C)).
; We will from now on ignore parameters and mention polynomials informally.

; In particular we define a polynomial
;   P[X,Y] = - Y^2 + X^3 + A*X + B
; and our main theorem shows that for x3, y3 properly defined,
;   P[x1,y1] =p 0 and P[x2,y2] =p 0 implies P[x3,y3] =p 0,
; where =p means equality modulo a prime p (definitions for =p and /p can be
; found in the file odd-prime-fields.lisp).

; Begin by supposing we have a line passing through the point (x1,y1) given by
;   y = alpha * x + beta.
; Then we must have
;   beta = y1 - alpha * x1
; where we let alpha be free. Now given a second point (x2,y2), we may define
;   alpha = (y2 - y1) / (x2 - x1),
; or if (x1, y1) = (x2, y2),
;   alpha = (3 x1^2 + A) / (2 y1),
; which we represent below as alpha{x1=/=x2} and alpha{x1=x2}, respectively.
; Now we define (where we abuse notation by writing P[X] and P[X,Y] to mean
; different polynomials)
;   P[X] = - (alpha * (X - x1) + y1)^2 + X^3 + A*X + B,
; which relates to P[X,Y] by a reparametrization of Y. In particular it
; immediately follows that
;   P[x1] = P[x1,y1] =p 0.

; First take the quotient of P[X] by (X - x1) to get
;   P[X] = Q[X] * (X - x1) + P[x1],
; and as a result we also have
;   P[X] =p Q[X] * (X - x1).
; Again take the quotient of Q[X] by (X - x2) to get
;   Q[X] = R[X] * (X - x2) + S
; where
;   R[X] = (X - x3)
;   S = alpha^2 * (x2 - x1) + x1^2 + x1*x2 + x2^2 - 2*alpha*y1 + A
; whenever x3 = alpha^2 - x1 - x2.

; We now consider two cases.
; First assume x1 =/=p x2, and thus alpha = (y2 - y1) / (x2 - x1), then we have
;   S * (x2 - x1) = - y1^2 + y2^2 + x1^3 - x2^3 + A*x1 - A*x2
;                 = (P[x1] - B) + (B - P[x2])
;                 =p 0.
; From which it follows that
;   Q[X] =p R[X] * (X - x2)
; and thus also
;   P[X] =p R[X] * (X - x2) * (X - x1)
; where we recall that R[X] = (X - x3), so we have
;   P[x3] =p 0.

; Now consider the case in which x1 =p x2, and thus also
;   alpha = (3*x1^2 + A) / (2*y1).
; We first compute (although it is not obvious at first sight) that
;   S =p 0
; then again we get
;   Q[X] =p R[X] * (X - x2)
; and again
;   P[X] =p R[X] * (X - x2) * (X - x1)
; and finally
;   P[x3] =p 0.

; We can now combine the two cases to get
; P[x1] =p 0, P[x2] =p 0 --> P[x3] =p 0.

; The reparametrized version can be achieved by noticing that whenever
;   Y = alpha * X + (y1 - alpha * x1),
; we have that
;   P[X, Y] =p 0 --> P[X] =p 0.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Computational lemmas.

;; compute special instances of 2 /p 2 and 6 /p 2
(defthmd *-of-/p-2-instance
  (implies (integerp x)
           (and (=p (i* 2 (/p 2) x) x)
                (=p (i* 6 (/p 2) x) (i* 3 x))))
  :hints (("Goal"
           :in-theory (enable i*)
           :use ((:instance *-of-/p-2 (n 2))
                 (:instance *-of-/p-2 (n 6))
                 (:instance =p-implies-=p-i*-1
                  (x (i* 2 (hide (/p 2))))
                  (x-equiv 1)
                  (y x))
                 (:instance =p-implies-=p-i*-1
                  (x (i* 6 (hide (/p 2))))
                  (x-equiv 3)
                  (y x))
                 (:instance integerp-of-/p (x 2)))
           :expand ((hide (/p 2)) (hide (=p 3 3))))))

;; expand 2 i* x
(defthmd *-2-x
  (=p (i* 2 x) (i+ x x))
  :hints (("Goal" :in-theory (enable i* i+)
           :cases ((equal (* 2 x) (+ x x))))))

;; expand 3 i* x
(defthmd *-3-x
  (=p (i* 3 x) (i+ x x x))
  :hints (("Goal" :in-theory (enable i* i+)
           :cases ((equal (* 3 x) (+ x x x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Abbreviations.

(defmacro isqr (x)
  `(i* ,x ,x))

(defmacro icube (x)
  `(i* ,x ,x ,x))

(defmacro domain-p (x1 y1 x2 y2 A B)
  `(and (integerp ,x1)
        (integerp ,y1)
        (integerp ,x2)
        (integerp ,y2)
        (integerp ,A)
        (integerp ,B)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Definitions.

(defund x3 (alpha x1 x2)
  (i- (isqr alpha)
      (i+ x1 x2)))

(defund y3 (alpha x1 y1 x2)
  (i- (i* alpha
          (i- x1 (x3 alpha x1 x2)))
      y1))

(defund P[X] (alpha x1 y1 A B X)
  (i+ (i- (isqr (i+ (i* alpha
                        (i- X x1))
                    y1)))
      (icube X)
      (i* A X)
      B))

(defund P[x1] (x1 y1 A B)
  (i+ (i- (isqr y1))
      (icube x1)
      (i* A x1)
      B))

(defund P[x2] (x2 y2 A B)
  (i+ (i- (isqr y2))
      (icube x2)
      (i* A x2)
      B))

(defund P[x3] (alpha x1 y1 x2 A B)
  (i+ (i- (isqr (i+ (i* alpha
                        (i- (x3 alpha x1 x2) x1))
                    y1)))
      (icube (x3 alpha x1 x2))
      (i* A (x3 alpha x1 x2))
      B))

(defun quotient (x1 y1 x2 y2 A B)
  (and (=p (P[x1] x1 y1 A B) 0)
       (=p (P[x2] x2 y2 A B) 0)))

(defund Q[X] (alpha x1 y1 A X)
  (i+ (isqr X)
      (i* (i- x1 (isqr alpha))
          X)
      (i+ (i* (isqr alpha) x1)
          (isqr x1)
          (i- (i* 2 alpha y1))
          A)))

(defund R[X] (alpha x1 x2 X)
  (i- X (x3 alpha x1 x2)))

(defund Delta-x (x1 x2)
  (i- x2 x1))

(defund alpha{x1=x2} (x1 y1 A)
  (i* (i+ (i* 3 (isqr x1))
          A)
      (/p (i* 2 y1))))

(defund alpha{x1=/=x2} (x1 y1 x2 y2)
  (i* (i- y2 y1)
      (/p (delta-x x1 x2))))

(defthm integerp-of-alpha{x1=x2}
  (integerp (alpha{x1=x2} x1 y1 A))
  :hints (("Goal" :in-theory (enable alpha{x1=x2}))))

(defthm integerp-of-alpha{x1=/=x2}
  (integerp (alpha{x1=/=x2} x1 y1 x2 y2))
  :hints (("Goal" :in-theory (enable alpha{x1=/=x2} delta-x))))

(defthm integerp-of-x3
  (integerp (x3 alpha x1 x2))
  :hints (("Goal" :in-theory (enable x3))))

(defthm integerp-of-y3
  (integerp (y3 alpha x1 y1 x2))
  :hints (("Goal" :in-theory (enable y3))))

(defthm integerp-of-delta-x
  (integerp (delta-x x1 x2))
  :hints (("Goal" :in-theory (enable delta-x))))

(defthm delta-x-non-zero-whenever-x1=/=x2
  (implies (not (=p x1 x2))
           (not (=p (delta-x x1 x2) 0)))
  :hints (("Goal"
           :in-theory (enable delta-x)
           :use ((:instance =p-implies-=p-i+-1
                  (x (i- x2 x1))
                  (x-equiv 0)
                  (y x1))))
          ("Subgoal 3" :in-theory (enable =p modp))
          ("Subgoal 2" :in-theory (enable i- =p modp))
          ("Subgoal 1" :in-theory (enable i+ i- =p modp)))
  :rule-classes ((:forward-chaining :trigger-terms ((=p x1 x2)))))

(defund S (alpha x1 y1 x2 A)
  (i+ (i* (isqr alpha)
          (i- (delta-x x1 x2)))
      (isqr x1)
      (i- (i* 2 alpha y1))
      (i* x1 x2)
      (isqr x2)
      A))

(defthm integerp-of-S
  (integerp (S alpha x1 y1 x2 A))
  :hints (("Goal" :in-theory (enable S delta-x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Proof.

;; R[X][x3/X] =p 0   (recall R[X] = (X - x3)
(defthmd step0-1
  (=p (R[X] alpha x1 x2 (x3 alpha x1 x2))
      0)
  :hints (("Goal" :in-theory (enable R[X]))))

;; technical lemma
;; P[x3] = P[X][x3/X]
(defthmd step0-2
  (=p (P[x3] alpha x1 y1 x2 A B)
      (P[X] alpha x1 y1 A B (x3 alpha x1 x2)))
  :hints (("Goal" :in-theory (enable P[x3] P[X]))))

;; P[X] = Q[X] * (X - x1) + P[x1]
(defthmd step1
  (equal (P[X] alpha x1 y1 A B X)
         (i+ (i* (Q[X] alpha x1 y1 A X) (i- X x1))
             (P[x1] x1 y1 A B)))
  :hints (("Goal" :in-theory (enable P[X] Q[X] P[x1] i+ i* i-))))

;; P[X] =p Q[X] * (X - x1)
(defthmd step2
  (implies (quotient x1 y1 x2 y2 A B)
           (=p (P[X] alpha x1 y1 A B X)
               (i* (Q[X] alpha x1 y1 A X) (i- X x1))))
  :hints (("Goal" :use step1)))

;; Q[X] = R[X] * (X - x2) + S
(defthmd step3
  (equal (Q[X] alpha x1 y1 A X)
         (i+ (i* (R[X] alpha x1 x2 X) (i- X x2))
             (S alpha x1 y1 x2 A)))
  :hints (("Goal" :in-theory (enable Q[X] R[X] S delta-x x3))
          ("Subgoal 3'" :in-theory (enable i* i+ i-))
          ("Subgoal 2'" :in-theory (enable i* i+ i-))
          ("Subgoal 1'" :in-theory (enable i* i+ i-))))

(encapsulate ()
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  ;; Case split with x1 =/=p x2
  ;; S * (x2 - x1) = - y1^2 + y2^2 + x1^3 - x2^3 + A*x1 - A*x2
  (defthmd step4.1
    (implies (and (domain-p x1 y1 x2 y2 A B)
                  (not (=p x1 x2))
                  (equal alpha (alpha{x1=/=x2} x1 y1 x2 y2)))
             (=p (i* (S alpha x1 y1 x2 A) (i- (delta-x x1 x2)))
                 (i+ (i- (isqr y1)) (isqr y2)
                     (icube x1) (i- (icube x2))
                     (i* A x1) (i- (* A x2)))))
    :hints (("Goal"
             :in-theory (e/d (S alpha{x1=/=x2})
                             (delta-x-non-zero-whenever-x1=/=x2))
             :use delta-x-non-zero-whenever-x1=/=x2)
            ("Goal'''" :in-theory (enable delta-x *-2-x))
            ("Goal'5'" :in-theory (enable i* i+ i-)))))

;; technical lemma
;; S * (x2 - x1) = (P[x1] - B) + (B - P[x2])
(Defthmd step5.1
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (not (=p x1 x2))
                (equal alpha (alpha{x1=/=x2} x1 y1 x2 y2)))
           (=p (i* (S alpha x1 y1 x2 A) (i- (delta-x x1 x2)))
               (i+ (i- (P[x1] x1 y1 A B) B)
                   (i- B (P[x2] x2 y2 A B)))))
  :hints (("Goal" :in-theory (enable P[x1] P[x2]) :use step4.1)
          ("Goal'''" :in-theory (enable i* i+ i-))))

;; P[x1] =p 0, P[x2] =p 0 --> S * (x2 - x1) =p 0
(Defthmd step6.1
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (not (=p x1 x2))
                (equal alpha (alpha{x1=/=x2} x1 y1 x2 y2))
                (quotient x1 y1 x2 y2 A B))
           (=p (i* (S alpha x1 y1 x2 A) (i- (delta-x x1 x2)))
               0))
  :hints (("Goal" :use step5.1)))

;; P[x1] =p 0, P[x2] =p 0, x1 p/= x2 --> S =p 0
(Defthmd step7.1
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (not (=p x1 x2))
                (equal alpha (alpha{x1=/=x2} x1 y1 x2 y2))
                (quotient x1 y1 x2 y2 A B))
           (=p (S alpha x1 y1 x2 A)
               0))
  :hints (("Goal" :use (step6.1
                        (:instance =p-implies-=p-i*-2
                         (x (i- (/p (delta-x x1 x2))))
                         (y (i* (s alpha x1 y1 x2 A) (i- (delta-x x1 x2))))
                         (y-equiv 0))))))

;; P[x1] =p 0, P[x2] =p 0, x1 p/= x2 --> Q[X] =p R[X] * (X - x2)
(defthmd step8.1
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (not (=p x1 x2))
                (equal alpha (alpha{x1=/=x2} x1 y1 x2 y2))
                (quotient x1 y1 x2 y2 A B))
           (=p (Q[X] alpha x1 y1 A X)
               (i* (R[X] alpha x1 x2 X) (i- X x2))))
  :hints (("Goal"  :use (step3 step7.1))))

;; P[x1] =p 0, P[x2] =p 0, x1 p/= x2 --> P[X] =p R[X] * (X - x2) * (X - x1)
(defthmd step9.1
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (not (=p x1 x2))
                (equal alpha (alpha{x1=/=x2} x1 y1 x2 y2))
                (quotient x1 y1 x2 y2 A B))
           (=p (P[X] alpha x1 y1 A B X)
               (i* (R[X] alpha x1 x2 X)
                   (i- X x2) (i- X x1))))
  :hints (("Goal" :use (step2 step8.1))))

;; P[x1] =p 0, P[x2] =p 0, x1 p/= x2 --> P[x3] =p 0  (because R[x3] =p 0)
(defthmd step10.1
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (not (=p x1 x2))
                (equal alpha (alpha{x1=/=x2} x1 y1 x2 y2))
                (quotient x1 y1 x2 y2 A B))
           (=p (P[x3] alpha x1 y1 x2 A B)
               0))
  :hints (("Goal" :use (step0-1
                        step0-2
                        (:instance step9.1 (X (x3 alpha x1 x2)))))))


;; Case split with x1 =p x2
;; x1 =p x2 --> S =p 0
;; This step  is not necessarily obvious to see, it just needs to be worked out.
(defthm step4.2
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (=p x1 x2)
                (not (=p y1 0))
                (equal alpha (alpha{x1=x2} x1 y1 A)))
           (=p (S alpha x1 y1 x2 A) 0))
  :hints (("Goal" :in-theory (enable S alpha{x1=x2} delta-x
                                     *-of-/p-2-instance *-3-x))))

;; x1 =p x2 --> Q[X] =p R[X] * (X - x2)
(defthm step5.2
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (=p x1 x2)
                (not (=p y1 0))
                (equal alpha (alpha{x1=x2} x1 y1 A)))
           (=p (Q[X] alpha x1 y1 A X)
               (i* (R[X] alpha x1 x2 X) (i- X x2))))
  :hints (("Goal" :use (step3 step4.2))))

;; P[x1] =p 0, P[x2] =p 0, x1 =p x2 --> P[X] =p R[X] * (X - x2) * (X - x1)
(defthm step6.2
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (=p x1 x2)
                (not (=p y1 0))
                (quotient x1 y1 x2 y2 A B)
                (equal alpha (alpha{x1=x2} x1 y1 A)))
           (=p (P[X] alpha x1 y1 A B X)
               (i* (R[X] alpha x1 x2 X) (i- X x2) (i- X x1))))
  :hints (("Goal" :use (step2 step5.2))))

;; P[x1] =p 0, P[x2] =p 0, x1 =p x2 --> P[x3] =p 0  (again because R[x3] =p 0)
(defthm step7.2
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (=p x1 x2)
                (not (=p y1 0))
                (quotient x1 y1 x2 y2 A B)
                (equal alpha (alpha{x1=x2} x1 y1 A)))
           (=p (P[x3] alpha x1 y1 x2 A B) 0))
  :hints (("Goal" :use (step0-1
                        step0-2
                        (:instance step6.2 (X (x3 alpha x1 x2)))))))

;; Main theorem: combine cases
;; P[x1] =p 0, P[x2] =p 0 --> P[x3] =p 0
;; no matter whether x1 = x2 or x1 =/= x2
(defthmd P[x1]=0-and-P[x2]=0-implies-P[x3]=0
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (=p (P[x1] x1 y1 A B) 0)
                (=p (P[x2] x2 y2 A B) 0)
                (implies (=p x1 x2)
                         (not (=p y1 0)))
                (implies (=p x1 x2)
                         (equal alpha (alpha{x1=x2} x1 y1 A)))
                (implies (not (=p x1 x2))
                         (equal alpha (alpha{x1=/=x2} x1 y1 x2 y2))))
           (=p (P[x3] alpha x1 y1 x2 A B) 0))
  :hints (("Goal" :use (step10.1 step7.2))))

;; Now we reparametrize this theorem

(defund P[X.Y] (X Y A B)
  (i+ (i- (isqr Y))
      (icube X)
      (i* A X)
      B))

(defcong =p =p (P[X.Y] X Y A B) 1
  :hints (("Goal" :in-theory (enable P[X.Y]))))

(defcong =p =p (P[X.Y] X Y A B) 2
  :hints (("Goal" :in-theory (enable P[X.Y]))))

;; P[X,Y] =p 0, Y =p alpha * X + y1 - alpha * x1 --> P[X] =p 0
(defthmd P[X.Y]=0-implies-P[X]=0
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (=p (P[X.Y] X Y A B) 0)
                (=p Y (i+ (i* alpha X) (i- y1 (i* alpha x1)))))
           (=p (P[X] alpha x1 y1 A B X) 0))
  :hints (("Goal" :in-theory (enable P[X] P[X.Y]))))

;; technical lemma
;; P[x1] = P[X][x1/X]
(defthmd P[x1]=P[X][X=x1]
  (implies (domain-p x1 y1 x2 y2 A B)
           (=p (P[X] alpha x1 y1 A B x1)
               (P[x1] x1 y1 A B)))
  :hints (("Goal" :in-theory (enable P[X] P[x1]))))

;; technical lemma
;; x1 p/= x2 --> y2 =p y1 + alpha * (x2 - x1)
(defthmd y2=alpha*x2+y1-alpha*x1
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (not (=p x1 x2)))
           (=p y2 (i+ y1 (i* (alpha{x1=/=x2} x1 y1 x2 y2)
                             (i- x2 x1)))))
  :hints (("Goal"
           :in-theory (enable alpha{x1=/=x2})
           :cases ((=p (i- x2 x1) (delta-x x1 x2))))
          ("Subgoal 2" :in-theory (enable delta-x))))

;; technical lemma
;; P[x2] = P[X][x2/X]
(defthmd P[x2]=P[X][X=x2]
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (implies (not (=p x1 x2))
                         (equal alpha (alpha{x1=/=x2} x1 y1 x2 y2)))
                (implies (=p x1 x2)
                         (equal alpha (alpha{x1=x2} x1 y1 A)))
                (implies (=p x1 x2)
                         (=p y1 y2)))
           (=p (P[X] alpha x1 y1 A B x2)
               (P[x2] x2 y2 A B)))
  :hints (("Goal" :in-theory (enable delta-x P[X] P[X2])
           :use y2=alpha*x2+y1-alpha*x1
           :cases ((=p x1 x2)))))

;; Reparametrization of the main theorem
;; P[x1,y1] =p 0, P[x2,y2] =p 0 --> P[x3,y3] =p 0
(defthmd P[X1.Y1]=0-and-P[X2.Y2]=0-implies-P[X3.Y3]=0
  (implies (and (domain-p x1 y1 x2 y2 A B)
                (=p (P[X.Y] x1 y1 A B) 0)
                (=p (P[X.Y] x2 y2 A B) 0)
                (implies (=p x1 x2)
                         (=p y1 y2))
                (implies (not (=p x1 x2))
                         (equal alpha (alpha{x1=/=x2} x1 y1 x2 y2)))
                (implies (=p x1 x2)
                         (equal alpha (alpha{x1=x2} x1 y1 A)))
                (implies (=p x1 x2)
                         (not (=p y1 0))))
           (=p (P[X.Y] (x3 alpha x1 x2) (y3 alpha x1 y1 x2) A B)
               0))
  :hints (("Goal"
           :in-theory (enable P[X.Y] P[x3] y3)
           :use ((:instance P[X.Y]=0-implies-P[X]=0 (X x1) (Y y1))
                 (:instance P[X.Y]=0-implies-P[X]=0 (X x2) (Y y2))
                 (:instance P[x1]=0-and-P[x2]=0-implies-P[x3]=0)
                 (:instance P[x1]=P[X][X=x1])
                 (:instance P[x2]=P[X][X=x2])
                 (:instance y2=alpha*x2+y1-alpha*x1)))))
