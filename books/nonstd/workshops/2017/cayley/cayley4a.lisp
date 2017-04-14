#|==========================================
 Cayley-Dickson Construction
   cayley4a.lisp

  1 April 2017

 Start with a composition algebra V.
 Let V2 be the set of cons pairs of elements from V.
 If V_multiplication is associative and commutative, 
    then V2 can be made into an associative composition algebra.

   Real Composition Algebra:
     A Real Vector Algebra with Identity:
       A Real Vector Space with Multiplication
       and a Multiplicative Identity.
   The Vector Algebra also has a real valued Norm
       and a real valued Dot (or Inner) Product
       satisfying the Composition Law
          Norm(xy) = Norm(x)Norm(y).

 References:

 J.H. Conway and D.A. Smith, On Quaternions and Octonions: Their Geometry,
 Arithmetic, and Symmetry, A K Peters, 2003, pages 67--73.

 H.-D. Ebbinghaus, H. Hermes, F. Hirzebruch, M. Koecher, K. Mainzer, 
 J. Neukirch, A. Prestel, and R. Remmert, Numbers, Springer, 1991, pp 265--274.     

ACL2 Version 7.4(r) built March 30, 2017  08:51:54.
System books directory "/home/acl2/acl2-7.4r/acl2-7.4/books/".
ACL2 Version 7.4 built March 29, 2017  10:38:07.
System books directory "/home/acl2/acl2-7.4/acl2-7.4/books/".
===============================|#
#|====================================
To certify:
(certify-book 
             "cayley4a"
             0   ;; world with no commands
             nil ;;compile-flg  
             ) 
===============================
To use:
(include-book 
        "cayley4a"  
        :uncertified-okp nil
        :defaxioms-okp nil 
        :skip-proofs-okp nil 
        ) 
=====================================|#
#|===============================================
:set-gag-mode t      ; enable gag-mode, suppressing most proof commentary
(set-gag-mode t)     ; same as above
:set-gag-mode :goals ; same as above, but print names of goals when produced
:set-gag-mode nil    ; disable gag-mode
==============|#
#|============================== 
(LD 
    "cayley4a.lisp")              ; read and evaluate each form in file 
==================|#

(in-package "ACL2")

(local
(include-book "arithmetic/top" :dir :system
         :uncertified-okp nil
         :defaxioms-okp nil
         :skip-proofs-okp nil))

#+non-standard-analysis
(local
(in-theory (disable REALP-IMPLIES-ACL2-NUMBERP)))

#-non-standard-analysis
(local
(in-theory (disable RATIONALP-IMPLIES-ACL2-NUMBERP)))

#|=======================
Distributivity of dot product over vector sum
 implies that the length of nonzero vectors
 can not all be the same nonzero constant.
Thus there is a vector with nonzero length different
from 1. 

if 0<(V_norm (V_+ (V_1)(V_1))<1, replace V_norm with 
  (V_norm_1 x) = 0 if x = V_0
  (V_norm_1 x) = (/ (V_norm x)) if x not= V_0

So we can assume (V_norm (V_+ (V_1)(V_1))>1

if 1<(V_norm (V_+ (V_1)(V_1))<2, replace V_norm with 
  (V_norm_2 x) = (expt (V_norm x) j)
 where j is an positive integer chosen so that
          (V_norm_2 (V_+ (V_1)(V_1)) >= 4

So we can assume that (V_norm (V_+ (V_1)(V_1))>= 4

could also Replace Norm(x) with Norm(x)^log_norm(2)_(4)
===========================|#
#|=============================
Add innerproduct axioms

<x,y> = 0   for norm(x) = |x|
<x,y> = x*y for norm(x) = x^2

V_dot is a positive definite symmetric bilenear form
V_dot is nonsingular
=====================|#

(encapsulate    
(;; Real Composition Algebra:
 ;;  A Real Vector Algebra with Identity:
 ;;    A Real Vector Space with Multiplication
 ;;    and a Multiplicative Identity.
 ;;  The Vector Algebra also has a real valued Norm
 ;;    and a real valued Dot (or Inner) Product
 ;;    satisfying the Composition Law
 ;;        Norm(xy) = Norm(x)Norm(y).
 ;;   10 functions and 22 axioms
 ;; ===============================
 ;; Real Vector Space Operations:
 ((Vp *)      => *)   ;; Predicate for set of vectors
 ((V_0)       => *)   ;; Zero vector
 ((V_+ * *)   => *)   ;; Vector addition
 ((V_- *)     => *)   ;; Vector minus
 ((S_* * *)   => *)   ;; Scalar multiplication
 ;; Vector Multiplication and Identity Operations:
 ((V_* * *)   => *)   ;; Vector multiplication
 ((V_1)       => *)   ;; One vector
 ;; Norm operation:
 ((V_norm *)  => *)   ;; Vector Norm
 ;; Dot (or Inner) Product Operation:
 ((V_dot * *) => *)   ;; Vector Dot Product
 ((Forall-u-V_dot-u-x=0 *) => *)   ;; Predicate with quantifier
 ((Forall-u-V_dot-u-x=0-witness *) => *)) ;; Skolem function 

(local 
 (defun 
   Vp (x)
   (real/rationalp x)))

(local
 (defun
   V_0 ()
   0))

(local
 (defun
   V_+ (x y)
   (+ x y)))

(local
 (defun
   V_- (x)
   (- x)))

(local
 (defun
   S_* (a x)
   (* a x)))

;; Real Vector Space Axioms:
(defthm  
  Vector-closure
  (and (Vp (V_0))
  (implies (and (Vp x)
          (Vp y))
     (Vp (V_+ x y)))
  (implies (Vp x)
     (Vp (V_- x)))
  (implies (and (real/rationalp a)
          (Vp x))
     (Vp (S_* a x)))))

(defthm
  Associativity-of-V_+
  (implies (and (Vp x)
     (Vp y)
     (Vp z))
      (equal (V_+ (V_+ x y) z)
       (V_+ x (V_+ y z)))))

(defthm
  Commutativity-of-V_+
  (implies (and (Vp x)
     (Vp y))
      (equal (V_+ x y)
       (V_+ y x))))

(defthm
  Unicity-of-V_0
  (implies (Vp x)
      (equal (V_+ (V_0) x)
       x)))

(defthm
  Inverse-of-V_+
  (implies (Vp x)
      (equal (V_+ x (V_- x))
       (V_0))))

(defthm
  Associativity-of-S_*
  (implies (and (real/rationalp a)
     (real/rationalp b)
     (Vp x))
      (equal (S_* a (S_* b x))
       (S_* (* a b) x))))

(defthm
  Unicity-of-Scalar-1
  (implies (Vp x)
      (equal (S_* 1 x) x)))

(defthm
  Distributivity-S_*-scalar-+
  (implies (and (real/rationalp a)
     (real/rationalp b)
     (Vp x))
      (equal (S_* (+ a b) x)
       (V_+ (S_* a x)(S_* b x)))))

(defthm
  Distributivity-S_*-V_+
  (implies (and (real/rationalp a)
     (Vp x)
     (Vp y))
      (equal (S_* a (V_+ x y))
       (V_+ (S_* a x)(S_* a y)))))

(local
 (defun
   V_* (x y)
   (* x y)))

(local
 (defun
   V_1 ()
   1))

;; Additional Real Vector Algebra Axioms:
(defthm
  V_1&V_*-closure
  (and (Vp (V_1))
  (implies (and (Vp x)
          (Vp y))
     (Vp (V_* x y)))))

(defthm
  Not-V_1=V_0
  (not (equal (V_1)(V_0))))

(defthm
  Left-Distributivity-V_*_V_+
  (implies (and (real/rationalp a)
     (real/rationalp b)
     (Vp x)
     (Vp y)
     (Vp z))
      (equal (V_* x 
      (V_+ (S_* a y)
           (S_* b z)))
       (V_+ (S_* a
           (V_* x y))
      (S_* b
           (V_* x z))))))

(defthm
  Right-Distributivity-V_*_V_+
  (implies (and (real/rationalp a)
     (real/rationalp b)
     (Vp x)
     (Vp y)
     (Vp z))
      (equal (V_* (V_+ (S_* a x)
           (S_* b y))
      z)
       (V_+ (S_* a
           (V_* x z))
      (S_* b
           (V_* y z))))))

(defthm
  Unicity-of-V_1
  (implies (Vp x)
      (and (equal (V_* (V_1) x) x)
     (equal (V_* x (V_1)) x))))

(local
 (defun
   V_norm (x)
   (* x x)))

;; Additional Vector Norm and Dot Product Axioms:
(defthm
  Realp>=0-V_norm
  (implies (Vp x)
      (and (real/rationalp (V_norm x))
     (>= (V_norm x) 0))))

(defthm
  V_norm=0
  (implies (Vp x)
      (equal (equal (V_norm x) 0)
       (equal x (V_0)))))

(defthm
  Composition-Law
  (implies (and (Vp x)
     (Vp y))
      (equal (V_norm (V_* x y))
       (* (V_norm x)
          (V_norm y)))))

(local
 (defun
   V_dot (x y)
   (* 1/2 (+ (V_norm (V_+ x y))
        (- (V_norm x))
        (- (V_norm y))))))

(defthm
  V_dot-def
  (equal (V_dot x y)
    (* 1/2 (+ (V_norm (V_+ x y))
        (- (V_norm x))
        (- (V_norm y)))))
  :rule-classes :definition)

(defthm
  Distributivity-V_dot-V_+
  (implies (and (real/rationalp a)
     (real/rationalp b)
     (Vp x)
     (Vp y)
     (Vp z))
      (equal (V_dot (V_+ (S_* a x)
             (S_* b y))
        z)
       (+ (* a (V_dot x z))
          (* b (V_dot y z))))))

(local
 (defthm
   V_dot=0
   (implies (Vp x)
       (equal (equal (V_dot x x) 0)
        (equal x (V_0))))))

(local
 (defun-sk 
   Forall-u-V_dot-u-x=0 (x)
   (forall (u)
      (implies (Vp u)
         (equal (V_dot u x) 0)))
   :rewrite :direct))

(defthm
  Forall-u-V_dot-u-x=0-def
  (equal (Forall-u-V_dot-u-x=0 x)
    (let ((u (Forall-u-V_dot-u-x=0-witness x)))
         (implies (Vp u)
      (equal (V_dot u x) 0))))
  :rule-classes :definition)

(defthm
  Forall-u-V_dot-u-x=0-necc
  (implies (Forall-u-V_dot-u-x=0 x)
      (implies (Vp u)
         (equal (V_dot u x) 0))))

(defthm  ;;V_dot is nonsingular
  Forall-u-V_dot-u-x=0->x=V_0
  (implies (and (Vp x)
     (Forall-u-V_dot-u-x=0 x))
      (equal x (V_0)))
  :rule-classes nil
  :hints (("Goal"
      :in-theory (disable V_dot=0)
      :use V_dot=0)))

(defthmD
  V_*-associativity
  (implies (and (Vp x)
     (Vp y)
     (Vp z))
      (equal (V_* (V_* x y) z)
       (V_* x (V_* y z)))))

(defthmD
  V_*-commutativity
  (implies (and (Vp x)
     (Vp y))
      (equal (V_* x y)
       (V_* y x))))

;; need (V_dot x x) >= 0 and (V_dot x x) = 0 iff x = (V_0)
;;    no longer needed -- use V_dot is nonsingular.
) ;; end encapsulate

;; (invisible-fns-table (w state))
(add-invisible-fns V_+ V_-)
(add-invisible-fns V_- V_-)
;; (invisible-fns-table (w state))

;; Real Vector Space Theorems:
(defthm
 Commutativity-2-of-V_+
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_+ x (V_+ y z))
      (V_+ y (V_+ x z))))
 :hints (("Goal"
     :in-theory (disable Commutativity-of-V_+) 
     :use (:theorem
     (implies (and (Vp x)
             (Vp y)
             (Vp z))
        (equal (V_+ (V_+ x y) z)
         (V_+ (V_+ y x) z)))))
    ("Subgoal 1"
     :in-theory (enable Commutativity-of-V_+) )))

(defthm
 V_-_cancellation-on-right
 (implies (and (Vp x)
    (Vp y))
     (equal (V_+ x (V_+ y (V_- x))) y)) 
 :hints (("Goal"
     :in-theory (disable Commutativity-2-of-V_+)
     :use (:instance
     Commutativity-2-of-V_+
     (z (V_- x))))))

(defthm
 V_-_cancellation-on-left
 (implies (and (Vp x)
    (Vp y))
     (equal (V_+ x (V_+ (V_- x) y)) y))
 :hints (("Goal"
     :in-theory (disable V_-_cancellation-on-right)
     :use V_-_cancellation-on-right)))

(defthm
 V_0-is-only-V_+_idempotent
 (implies (Vp x)
     (equal (equal (V_+ x x) x)
      (equal x (V_0))))
 :hints (("Goal"
     :use (:instance
     (:theorem
      (implies (equal x y)
         (equal (V_+ x z)(V_+ y z))))
     (x (V_+ x x))
     (y x)
     (z (V_- x))))))

(defthm
 S_*-0=V_0
 (implies (Vp x)
     (equal (S_* 0 x)(V_0)))
 :hints (("Goal"
     :in-theory (disable Distributivity-S_*-scalar-+)
    :use (:instance
    Distributivity-S_*-scalar-+
    (a 0)
    (b 0)))))

(defthm
 S_*-V_0=V_0
 (implies (real/rationalp a)
     (equal (S_* a (V_0))(V_0)))
 :hints (("Goal"
     :in-theory (disable Distributivity-S_*-V_+)
     :use (:instance
     Distributivity-S_*-V_+
     (x (V_0))
     (y (V_0))))))

(defthm
 V_-_is-unique
 (implies (and (Vp x)
    (Vp y))
     (equal (equal (V_+ x y)(V_0))
      (equal y (V_- x))))
 :hints (("Goal"
     :use (:instance
     (:theorem
      (implies (equal x y)
         (equal (V_+ x z)(V_+ y z))))
     (x (V_+ x y))
     (y (v_0))
     (z (V_- x))))))

(defthm
 S_*_-a=V_-_S_*
 (implies (and (real/rationalp a)
    (Vp x))
     (equal (S_* (- a) x)(V_- (S_* a x))))
 :hints (("Goal"
     :in-theory (disable Distributivity-S_*-scalar-+)
     :use (:instance
     Distributivity-S_*-scalar-+
     (b (- a))))))

(defthm
 S_*_V_-=V_-_S_*
 (implies (and (real/rationalp a)
    (Vp x))
     (equal (S_* a (V_- x))(V_- (S_* a x))))
 :hints (("Goal"
     :in-theory (disable Distributivity-S_*-V_+)
     :use (:instance
     Distributivity-S_*-V_+
     (y (V_- x))))))

(defthm
 Distributivity-V_-_over-V_+
 (implies (and (Vp x)
    (Vp y))
     (equal (V_- (V_+ x y))(V_+ (V_- x)(V_- y))))
 :hints (("Goal"
     :in-theory (disable V_-_is-unique)
     :use (:instance
     V_-_is-unique
     (x (V_+ x y))
     (y (V_+ (V_- x)(V_- y)))))))

(defthm
 V_-_V_-_x=x
 (implies (Vp x)
     (equal (V_- (V_- x)) x))
 :hints (("Goal"
     :in-theory (disable V_-_is-unique)
     :use (:instance
     V_-_is-unique
     (x (V_- x))
     (y x)))))

;; Vector multiplication theorems:
(defthm
 V_*-S_*=S_*-V_*-left
 (implies (and (real/rationalp a)
    (Vp x)
    (Vp y))
     (equal (V_* (S_* a x) y)
      (S_* a (V_* x y))))
 :hints (("Goal"
     :in-theory (disable Right-Distributivity-V_*_V_+)
     :use (:instance
     Right-Distributivity-V_*_V_+
     (b 0)
     (z y)))))

(defthm
 V_*-S_*=S_*-V_*-right
 (implies (and (real/rationalp a)
    (Vp x)
    (Vp y))
     (equal (V_* x (S_* a y))
      (S_* a (V_* x y))))
 :hints (("Goal"
     :in-theory (disable Left-Distributivity-V_*_V_+)
     :use (:instance
     Left-Distributivity-V_*_V_+
     (b 0)
     (z y)))))

(defthm
 V_*-V_0=V_0-left
 (implies (Vp x)
     (equal (V_* (V_0) x)(V_0)))
 :hints (("Goal"
     :in-theory (disable Right-Distributivity-V_*_V_+)
     :use (:instance
     Right-Distributivity-V_*_V_+
     (a 1)
     (b 1)
     (x (V_0))
     (y (V_0))
     (z x)))))

(defthm
 V_*-V_0=V_0-right
 (implies (Vp x)
     (equal (V_* x (V_0))(V_0)))
 :hints (("Goal"
     :in-theory (disable Left-Distributivity-V_*_V_+)
     :use (:instance
     Left-Distributivity-V_*_V_+
     (a 1)
     (b 1)
     (y (V_0))
     (z (V_0))))))

(defthm
 V_*-V_-=V_-V_*-left
 (implies (and (Vp x)
    (Vp y))
     (equal (V_* (V_- x) y)
      (V_- (V_* x y))))
 :hints (("Goal"
     :in-theory (disable Right-Distributivity-V_*_V_+)
     :use (:instance
     Right-Distributivity-V_*_V_+
     (a 1)
     (b 1)
     (y (V_- x))
     (z y)))))

(defthm
 V_*-V_-=V_-V_*-right
 (implies (and (Vp x)
    (Vp y))
     (equal (V_* x (V_- y))
      (V_- (V_* x y))))
 :hints (("Goal"
     :in-theory (disable Left-Distributivity-V_*_V_+)
     :use (:instance
     Left-Distributivity-V_*_V_+
     (a 1)
     (b 1)
     (y (V_- y))
     (z y)))))

;; Vector Norm and Dot Product theorems:
(defthm
 V_norm-V_1=1
 (equal (V_norm (V_1)) 1)
 :hints (("Goal"
     :in-theory (disable Composition-Law)
     :use (:instance
     Composition-Law
     (x (V_1))
     (y (V_1))))))

(defthm
 V_norm-V_0=0
 (equal (V_norm (V_0)) 0))

(defthmD
 Realp>=0-V_norm-forward-chaining
 (implies (Vp x)
     (and (real/rationalp (V_norm x))
    (>= (V_norm x) 0)))
 :rule-classes :forward-chaining)

(defthm
 V_0-is-only-zero-divisor
 (implies (and (Vp x)
    (Vp y))
     (equal (equal (V_* x y)(V_0))
      (or (equal x (V_0))
          (equal y (V_0)))))
 :hints (("Goal"
     :in-theory (e/d (Realp>=0-V_norm-forward-chaining)
         (ZERO-IS-ONLY-ZERO-DIVISOR
          Composition-Law))
     :use (Composition-Law
     (:instance
      ZERO-IS-ONLY-ZERO-DIVISOR
      (x (V_norm x))
      (y (V_norm y)))))))

(defthm
 Realp-V_dot
 (implies (and (Vp x)
    (Vp y))
     (real/rationalp (V_dot x y))))

(defthmD
 Realp-V_dot-forward-chaining
 (implies (and (Vp x)
    (Vp y))
     (real/rationalp (V_dot x y)))
 :rule-classes :forward-chaining)

(defthm
 Commmutativity-of-Vdot
 (implies (and (Vp x)
    (Vp y))
     (equal (V_dot x y)
      (V_dot y x))))

(defthm
 V_dot-V_0
 (implies (Vp x)
     (equal (V_dot x (V_0)) 0)))

(defthm
 Scaling-law-left
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot (V_* x y)
       (V_* x z))
      (* (V_norm x)
         (V_dot y z))))
 :hints (("Subgoal 2"
     :in-theory (disable LEFT-DISTRIBUTIVITY-V_*_V_+)
     :use (:instance
     LEFT-DISTRIBUTIVITY-V_*_V_+
     (a 1)
     (b 1)))
    ("Subgoal 1"
     :use (:theorem
     (implies (and (Vp x)
             (Vp y)
             (Vp z))
        (real/rationalp (V_norm (V_+ (V_* X Y) (V_* X Z)))))))))

(defthm
 Scaling-law-right
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot (V_* x z)
       (V_* y z))
      (* (V_dot x y)
         (V_norm z))))
 :hints (("Subgoal 2"
     :in-theory (disable right-DISTRIBUTIVITY-V_*_V_+)
     :use (:instance
     right-DISTRIBUTIVITY-V_*_V_+
     (a 1)
     (b 1)))
    ("Subgoal 1"
     :use (:theorem
     (implies (and (Vp x)
             (Vp y)
             (Vp z))
        (real/rationalp (V_norm (V_+ (V_* X z) (V_* y Z)))))))))

(defthm
 Distributivity-V_dot-V_+-right
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot x 
       (V_+ (S_* a y)
            (S_* b z)))
      (+ (* a (V_dot x y))
         (* b (V_dot x z)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             Distributivity-V_dot-V_+)
     :use (:instance 
     Distributivity-V_dot-V_+
     (x y)
     (y z)
     (z x)))))

(defthm
 Distributivity-V_dot-V_+-left&right
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (real/rationalp c)
    (real/rationalp d)
               (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot (V_+ (S_* a u)
            (S_* b x))
       (V_+ (S_* c y)
            (S_* d z)))
      (+ (* a c (V_dot u y))
         (* a d (V_dot u z))
         (* b c (V_dot x y))
         (* b d (V_dot x z)))))        
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)))))

(defthm
 Exchange-Law-Lemma-a
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot (V_* (V_+ u x) y)
       (V_* (V_+ u x) z))
      (V_dot (V_+ (V_* u y)
            (V_* x y))
       (V_+ (V_* u z)
            (V_* x z)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             SCALING-LAW-LEFT
             Right-Distributivity-V_*_V_+)
    :use ((:instance
     Right-Distributivity-V_*_V_+
     (a 1)
     (b 1)
     (x u)
     (y x)
     (z y))
    (:instance
     Right-Distributivity-V_*_V_+
     (a 1)
     (b 1)
     (x u)
     (y x))))))

(defthm
 Exchange-Law-Lemma-b
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot (V_+ (V_* u y)
            (V_* x y))
       (V_+ (V_* u z)
            (V_* x z)))
      (+ (V_dot (V_* u y)
          (V_* u z))
         (V_dot (V_* u y)
          (V_* x z))
         (V_dot (V_* x y)
          (V_* u z))
         (V_dot (V_* x y)
          (V_* x z)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             SCALING-LAW-LEFT
             Distributivity-V_dot-V_+-left&right)
     :use (:instance
     Distributivity-V_dot-V_+-left&right
     (a 1)
     (b 1)
     (c 1)
     (d 1)
     (u (V_* u y))
     (x (V_* x y))
     (y (V_* u z))
     (z (V_* x z))))))

(defthm
 Exchange-Law-Lemma-c
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot (V_* (V_+ u x) y)
       (V_* (V_+ u x) z))
      (+ (V_dot (V_* u y)
          (V_* u z))
         (V_dot (V_* u y)
          (V_* x z))
         (V_dot (V_* x y)
          (V_* u z))
         (V_dot (V_* x y)
          (V_* x z))))))

(defthm
 Exchange-Law-Lemma-d
 (implies (and (Vp u)
    (Vp x))
     (equal (+ (V_norm u)
         (* 2 (V_dot u x))
         (V_norm x))
      (V_norm (V_+ u x))))
 :hints (("Goal"
     :in-theory (e/d (Realp>=0-V_norm-forward-chaining)
         (REALP>=0-V_NORM))
     :use (:instance
     REALP>=0-V_NORM
     (x (V_+ u x))))))

(defthm
 Exchange-Law-Lemma-e
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (+ (V_dot (V_* u y)
          (V_* u z))
         (V_dot (V_* u y)
          (V_* x z))
         (V_dot (V_* x y)
          (V_* u z))
         (V_dot (V_* x y)
          (V_* x z)))
      (* (+ (V_norm u)
      (* 2 (V_dot u x))
      (V_norm x))
         (V_dot y z))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             SCALING-LAW-LEFT
             Exchange-Law-Lemma-d)
     :use ((:instance 
      SCALING-LAW-LEFT
      (x (V_+ u x)))
     Exchange-Law-Lemma-d))))

(defthm
 Exchange-Law
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (+ (V_dot (V_* u y)
          (V_* x z))
         (V_dot (V_* u z)
          (V_* x y)))
      (* 2
         (V_dot u x)
         (V_dot y z))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             Exchange-Law-Lemma-e)
     :use Exchange-Law-Lemma-e)))

(defun
 V_conjugate (x)
 (V_+ (S_* (* 2 (V_dot x (V_1)))
      (V_1))
      (V_- x)))

(defthm
 Vp-V_conjugate
 (implies (Vp x)
     (Vp (V_conjugate x))))

(defthm
 V_conjugate-V_0=V_0
 (equal (V_conjugate (V_0))
   (V_0)))

(defthm
 V_dot-S_*=*-V_dot-left
 (implies (and (real/rationalp a)
    (Vp x)
    (Vp y))
     (equal (V_dot (S_* a x) y)
      (* a (V_dot x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             DISTRIBUTIVITY-V_DOT-V_+)
     :use (:instance
     DISTRIBUTIVITY-V_DOT-V_+
     (b 0)
     (z y)))))

(defthm
 V_dot-S_*=*-V_dot-right
 (implies (and (real/rationalp a)
    (Vp x)
    (Vp y))
     (equal (V_dot x (S_* a y))
      (* a (V_dot x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             V_dot-S_*=*-V_dot-left)
     :use (:instance
     V_dot-S_*=*-V_dot-left
     (x y)
     (y x)))))

(defthm
 V_dot-V_-=-_V_dot-right
 (implies (and (Vp x)
    (Vp y))
     (equal (V_dot x (V_- y))
      (- (V_dot x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             V_dot-S_*=*-V_dot-right)
     :use (:instance
     V_dot-S_*=*-V_dot-right
     (a -1)))))

(defthm
 V_dot-V_-=-_V_dot-left
 (implies (and (Vp x)
    (Vp y))
     (equal (V_dot (V_- x) y)
      (- (V_dot x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)))))

(defthm
 Sum-conjugation
 (implies (and (Vp x)
    (Vp y))
     (equal (V_conjugate (V_+ x y))
      (V_+ (V_conjugate x)
           (V_conjugate y))))
:hints (("Goal"
    :in-theory (disable (:DEFINITION V_DOT-DEF)
            Distributivity-V_dot-V_+-right)
    :use (:instance
    Distributivity-V_dot-V_+-right
    (x (V_1))
    (a 1)
    (b 1)
    (y x)
    (z y)))))

(defthmD
 Braid-Law-1-lemma-a
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot y (V_* (V_conjugate x) z))
      (V_dot y (V_+ (S_* (* 2 (V_dot x (V_1)))
             z)
        (V_- (V_* x z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             Right-Distributivity-V_*_V_+)
     :use (:instance
     Right-Distributivity-V_*_V_+
     (a 1)
     (b (* 2 (V_DOT (V_1) x)))
     (x (V_- x))
     (y (V_1))))))

(defthmD
 Braid-Law-2-lemma-a
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot x (V_* z (V_conjugate y)))
      (V_dot x (V_+ (S_* (* 2 (V_dot y (V_1)))
             z)
        (V_- (V_* z y))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             Left-Distributivity-V_*_V_+)
     :use (:instance
     Left-Distributivity-V_*_V_+
     (a 1)
     (b (* 2 (V_dot y (V_1))))
     (x z)
     (y (V_- y))
     (z (V_1))))))

(defthmD
 Braid-Law-1-lemma-b
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot y (V_* (V_conjugate x) z))
      (+ (* 2 
      (V_dot x (V_1))
      (V_dot y z))
         (- (V_dot y (V_* x z))))))
 :hints (("Goal"
     :in-theory (e/d (Braid-Law-1-lemma-a)
         ((:DEFINITION V_DOT-DEF)
          (:DEFINITION V_CONJUGATE)
          Distributivity-V_dot-V_+-right))
     :use (:instance
     Distributivity-V_dot-V_+-right
     (a 1)
     (b 1)
     (x y)
     (y (V_- (V_* x z)))
     (z (S_* (* 2 (V_DOT (V_1) x)) z))))))

(defthmD
 Braid-Law-2-lemma-b
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot x (V_* z (V_conjugate y)))
      (+ (* 2 
      (V_dot y (V_1))
      (V_dot x z))
         (- (V_dot x (V_* z y))))))
 :hints (("Goal"
     :in-theory (e/d (Braid-Law-2-lemma-a)
         ((:DEFINITION V_DOT-DEF)
          (:DEFINITION V_CONJUGATE)
          Distributivity-V_dot-V_+-right))
     :use (:instance
     Distributivity-V_dot-V_+-right
     (a 1)
     (b 1)
     (y (V_- (V_* z y)))
     (z (S_* (* 2 (V_DOT (V_1) y)) z))))))

(defthm
 Braid-Law-1
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot y (V_* (V_conjugate x) z))
      (V_dot z (V_* x y))))
 :hints (("Goal"
     :in-theory (e/d (Braid-Law-1-lemma-b)
         ((:DEFINITION V_DOT-DEF)
          (:DEFINITION V_CONJUGATE)
          Exchange-Law))
     :use (:instance
     Exchange-Law
     (u (V_1))))))

(defthm
 Braid-Law-2
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot x (V_* z (V_conjugate y)))
      (V_dot z (V_* x y))))
 :hints (("Goal"
     :in-theory (e/d (Braid-Law-2-lemma-b)
         ((:DEFINITION V_DOT-DEF)
          (:DEFINITION V_CONJUGATE)
          Exchange-Law))
     :use (:instance
     Exchange-Law
     (u z)
     (z (V_1))))))

(defthm
 Braid-Law-3
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot (V_conjugate x) (V_* y (V_conjugate z)))
      (V_dot z (V_* x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)))))

(defthm
 Braid-Law-4
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot (V_conjugate y) (V_* (V_conjugate z) x))
      (V_dot z (V_* x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)))))

(defthm
 Braid-Law-5
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot (V_conjugate z) (V_* (V_conjugate y)(V_conjugate x)))
      (V_dot z (V_* x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)))))

(defthm
 BiConjugation-lemma
 (implies (and (Vp x)
    (Vp u))
     (equal (V_dot u (V_conjugate (V_conjugate x)))
      (V_dot u x)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)
             Braid-Law-1)
     :use ((:instance
      Braid-Law-1
      (y (V_1))
      (z u))
     (:instance
      Braid-Law-1
      (x (V_conjugate x))
      (y u)
      (z (V_1)))))))

(defun-sk
 Forall-u-V_dot-u-x=V_dot-u-y (x y)
 (forall (u)
    (implies (Vp u)
       (equal (V_dot u x)
        (V_dot u y))))
 :rewrite :direct)

(defthm
 Forall-u-V_dot-u-x=V_dot-u-y->Forall-u-V_dot-u-x=0-lemma
 (implies (and (Vp x)
    (Vp y)
    (Forall-u-V_dot-u-x=V_dot-u-y x y))
     (implies (Vp u)
        (equal (V_dot u (V_+ x
           (V_- y)))
         0)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION FORALL-U-V_DOT-U-X=V_DOT-U-Y)
             Forall-u-V_dot-u-x=V_dot-u-y-necc
             Distributivity-V_dot-V_+-right)
     :use (Forall-u-V_dot-u-x=V_dot-u-y-necc
     (:instance
      Distributivity-V_dot-V_+-right
      (x u)
      (a 1)
      (b -1)
      (y x)
      (z y))))))

(defthm
 Forall-u-V_dot-u-x=V_dot-u-y->Forall-u-V_dot-u-x=0
 (implies (and (Vp x)
    (Vp y)
    (Forall-u-V_dot-u-x=V_dot-u-y x y))
     (Forall-u-V_dot-u-x=0 (V_+ x
              (V_- y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION FORALL-U-V_DOT-U-X=V_DOT-U-Y)))))

(defthm
 Forall-u-V_dot-u-x=V_dot-u-y->x=y
 (implies (and (Vp x)
    (Vp y)
    (Forall-u-V_dot-u-x=V_dot-u-y x y))
     (equal x y))
 :rule-classes nil
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION FORALL-U-V_DOT-U-X=V_DOT-U-Y)
             V_-_IS-UNIQUE)
     :use ((:instance
      Forall-u-V_dot-u-x=0->x=V_0
      (x (V_+ x (V_- y))))
     (:instance
      V_-_IS-UNIQUE
      (y x)
      (x (V_- y)))))))

(defthm
 BiConjugation
 (implies (Vp x)
     (equal (V_conjugate (V_conjugate x))
      x))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE))
     :use (:instance
     Forall-u-V_dot-u-x=V_dot-u-y->x=y
     (x (V_conjugate (V_conjugate x)))
     (y x)))))

(defthmD
 Product-conjugation-lemma-a
 (implies (and (Vp u)
    (Vp x)
    (Vp y))
     (equal (V_dot u
       (V_* (V_conjugate y)
            (V_conjugate x)))
      (V_dot (V_conjugate x)
       (v_* y u))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)
             Braid-Law-2))))

(defthmD
 Product-conjugation-lemma-b
 (implies (and (Vp u)
    (Vp x)
    (Vp y))
     (equal (V_dot (V_conjugate x)
       (v_* y u))
      (V_dot y
       (V_* (V_conjugate x)
            (V_conjugate u)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)))))

(defthmD
 Product-conjugation-lemma-c
 (implies (and (Vp u)
    (Vp x)
    (Vp y))
     (equal (V_dot y
       (V_* (V_conjugate x)
            (V_conjugate u)))
      (V_dot (V_conjugate u)
       (v_* x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)
             Braid-Law-2))))

(defthmD
 Product-conjugation-lemma-d
 (implies (and (Vp u)
    (Vp x)
    (Vp y))
     (equal (V_dot (V_conjugate u)
       (v_* x y))
      (V_dot (V_conjugate u)
       (V_* (v_* x y)(V_1)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)))))

(defthmD
 Product-conjugation-lemma-e
 (implies (and (Vp u)
    (Vp x)
    (Vp y))
     (equal (V_dot (V_conjugate u)
       (V_* (v_* x y)(V_1)))
      (V_dot (V_1)
       (V_* (V_conjugate u)
            (V_conjugate (V_* x y))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)))))

(defthmD
 Product-conjugation-lemma-f
 (implies (and (Vp u)
    (Vp x)
    (Vp y))
     (equal (V_dot (V_1)
       (V_* (V_conjugate u)
            (V_conjugate (V_* x y))))
      (V_dot u
       (V_conjugate (V_* x y)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)
             Braid-Law-2))))

(defthm
 Product-conjugation-lemma
 (implies (and (Vp u)
    (Vp x)
    (Vp y))
     (equal (V_dot u
       (V_* (V_conjugate y)
            (V_conjugate x)))
      (V_dot u
       (V_conjugate (V_* x y)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)
             Braid-Law-1
             Braid-Law-2)
     :use (Product-conjugation-lemma-a
     Product-conjugation-lemma-b
     Product-conjugation-lemma-c
     Product-conjugation-lemma-d
     Product-conjugation-lemma-e
     Product-conjugation-lemma-f))))

(defthm
 Product-conjugation
 (implies (and (Vp x)
    (Vp y))
     (equal (V_conjugate (V_* x y))
      (V_* (V_conjugate y)
           (V_conjugate x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE))
     :use (:instance
     Forall-u-V_dot-u-x=V_dot-u-y->x=y
     (x (V_conjugate (V_* x y)))
     (y (V_* (V_conjugate y)
       (V_conjugate x)))))))

(in-theory (disable Product-conjugation-lemma))

(defthm
 Inverse-law-left-lemma-a
 (implies (and (Vp u)
    (Vp x)
    (Vp y))
     (equal (V_dot u (V_* (V_conjugate x)
        (V_* x y)))
      (* (V_norm x)(V_dot u y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)))))

(defthm
 Inverse-law-left-lemma-b
 (implies (and (Vp u)
    (Vp x)
    (Vp y))
     (equal (V_dot u (V_* (V_conjugate x)
        (V_* x y)))
      (V_dot u (S_* (V_norm x) y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)))))

(defthm
 Inverse-law-left
 (implies (and (Vp x)
    (Vp y))
     (equal (V_* (V_conjugate x)
           (V_* x y))
      (S_* (V_norm x) y)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE))
     :use (:instance
     Forall-u-V_dot-u-x=V_dot-u-y->x=y
     (x (V_* (V_conjugate x)
       (V_* x y)))
     (y (S_* (V_norm x) y)))))) 

(defthm
 Inverse-law-right-lemma-a
 (implies (and (Vp u)
    (Vp x)
    (Vp y))
     (equal (V_dot u (V_* (V_* y x)
        (V_conjugate x)))
      (* (V_norm x)(V_dot u y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)))))

(defthm
 Inverse-law-right-lemma-b
 (implies (and (Vp u)
    (Vp x)
    (Vp y))
     (equal (V_dot u (V_* (V_* y x)
        (V_conjugate x)))
      (V_dot u (S_* (V_norm x) y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)))))

(defthm
 Inverse-law-right
 (implies (and (Vp x)
    (Vp y))
     (equal (V_* (V_* y x)
           (V_conjugate x))
      (S_* (V_norm x) y)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE))
     :use (:instance
     Forall-u-V_dot-u-x=V_dot-u-y->x=y
     (x (V_* (V_* y x)
       (V_conjugate x)))
     (y (S_* (V_norm x) y)))))) 

(defun
 V_/ (x)
 (if (and (Vp x)
     (not (equal x (V_0))))
     (S_* (/ (V_norm x))
     (V_conjugate x))
     (V_0)))

(defthm
 Vp-V_/
 (Vp (V_/ x))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)
             (:DEFINITION V_DOT-DEF)))))

(defthm
 V_norm>0
 (implies (and (Vp x)
    (not (equal x (V_0))))
     (> (V_norm x) 0))
 :rule-classes (:linear :rewrite)
 :hints (("Goal"
     :in-theory (disable V_norm=0)
     :use V_norm=0)))

(defthm
 Inverse-law-left-1
 (implies (and (Vp x)
    (not (equal x (V_0)))
    (Vp y))
     (equal (V_* (V_/ x)
           (V_* x y))
      y))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)
             V_norm>0)
     :use V_norm>0)))

(defthm
 Inverse-law-right-1
 (implies (and (Vp x)
    (not (equal x (V_0)))
    (Vp y))
     (equal (V_* (V_* y x)
           (V_/ x))
      y))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)
             V_norm>0)
     :use V_norm>0)))

(defthm
 Inverse-law-left-2
 (implies (Vp x)
     (equal (V_* (V_conjugate x) x)
      (S_* (V_norm x) (V_1))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)
             Inverse-law-left)
     :use (:instance
     Inverse-law-left
     (y (V_1))))))

(defthm
 Inverse-law-right-2
 (implies (Vp x)
     (equal (V_* x (V_conjugate x))
      (S_* (V_norm x) (V_1))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)
             Inverse-law-right)
     :use (:instance
     Inverse-law-right
     (y (V_1))))))

(defthm
 Inverse-law-left-3
 (implies (and (Vp x)
    (not (equal x (V_0))))
     (equal (V_* (V_/ x) x)
      (V_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_/)
             Inverse-law-left-1)
     :use (:instance
     Inverse-law-left-1
     (y (V_1))))))

(defthm
 Inverse-law-right-3
 (implies (and (Vp x)
    (not (equal x (V_0))))
     (equal (V_* x (V_/ x))
      (V_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_/)
             Inverse-law-right-1)
     :use (:instance
     Inverse-law-right-1
     (y (V_1))))))

(defthm
 V_conjugate-V_1-is-V_*-idempotent
 (equal (V_* (V_conjugate (V_1))
        (V_conjugate (V_1)))
   (V_conjugate (V_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)
             Product-conjugation)
    :use (:instance
    Product-conjugation
    (x (V_1))
    (y (V_1))))))

(defthm
 not-V_Conjugate-V_1=V_0
 (not (equal (V_conjugate (V_1))(V_0)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)
             BiConjugation)
     :use (:instance
     BiConjugation
     (x (V_1))))))

(defthm
 V_0&V_1-only-V_*_idempotents
 (implies (Vp x)
     (equal (equal (V_* x x) x)
      (or (equal x (V_0))
          (equal x (V_1)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_/)
             Inverse-law-left-1)
     :use (:instance
     Inverse-law-left-1
     (y x)))))

(defthm
 V_conjugate-V_1=V_1
 (equal (V_conjugate (V_1))
   (V_1))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)
             V_0&V_1-only-V_*_idempotents)
    :use (:instance
    V_0&V_1-only-V_*_idempotents
    (x (V_conjugate (V_1)))))))

(defthm
 S_*=V_0-equals-a=0-or-x=V_0
 (implies (and (real/rationalp a)
    (Vp x))
     (equal (equal (S_* a x)(V_0))
      (or (equal a 0)
          (equal x (V_0)))))
 :hints (("Goal"
     :in-theory (disable Associativity-of-S_*)
     :use (:instance
     Associativity-of-S_*
     (a (/ a))
     (b a)))))

(defthm
 S_*=S_*-equals-a=b-or-x=V_0
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (Vp x))
     (equal (equal (S_* a x)(S_* b x))
      (or (equal a b)
          (equal x (V_0)))))
 :hints (("Goal"
     :in-theory (disable S_*=V_0-equals-a=0-or-x=V_0)
     :use (:instance
     S_*=V_0-equals-a=0-or-x=V_0
     (a (- a b))))))

(defthm
 V_norm-V_conjugate=V_norm
 (implies (Vp x)
     (equal (V_norm (V_conjugate x))
      (V_norm x)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)
             S_*=S_*-equals-a=b-or-x=V_0
             INVERSE-LAW-LEFT-2
             INVERSE-LAW-RIGHT-2)
    :use ((:instance
     S_*=S_*-equals-a=b-or-x=V_0
     (a (V_norm x))
     (b (V_norm (V_conjugate x)))
     (x (V_1)))
    (:instance
     INVERSE-LAW-LEFT-2
     (x (V_conjugate x)))
    INVERSE-LAW-RIGHT-2))))

(defthm
 Alternative-law-1-lemma-a
 (implies (and (Vp x)
    (Vp y))
     (equal (V_* (V_conjugate x)
           (V_* x y))
      (V_* (V_* (V_conjugate x)
          x)
           y)))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V_CONJUGATE)))))

(defthm
 Alternative-law-1-lemma-b
 (implies (and (Vp x)
    (Vp y))
     (equal (V_* (V_conjugate x)
           (V_* x y))
      (V_+ (V_- (V_* X (V_* X Y)))
           (S_* (* 2 (V_DOT (V_1) X))
          (V_* X Y)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             Right-Distributivity-V_*_V_+)
     :use (:instance
      Right-Distributivity-V_*_V_+
      (a 1)
      (b (* 2 (V_DOT (V_1) X)))
      (x (V_- X))
      (y (V_1))
      (z (V_* x y))))))

(defthm
 Alternative-law-1-lemma-c
 (implies (Vp x)
     (equal (V_* (V_conjugate x) x)
      (V_+ (V_- (V_* x x))
           (S_* (* 2 (V_DOT (V_1) X)) x))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             Right-Distributivity-V_*_V_+)
     :use (:instance
      Right-Distributivity-V_*_V_+
      (a 1)
      (b (* 2 (V_DOT (V_1) X)))
      (x (V_- X))
      (y (V_1))
      (z x)))))

(defthm
 Alternative-law-1-lemma-d
 (implies (and (Vp x)
    (Vp y))
     (equal (V_* (V_* (V_conjugate x) x)
           y)
      (V_+ (V_- (V_* (V_* x x) y))
           (S_* (* 2 (V_DOT (V_1) X)) 
          (V_* x y)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)
             Right-Distributivity-V_*_V_+)
     :use (:instance
      Right-Distributivity-V_*_V_+
      (a 1)
      (b (* 2 (V_DOT (V_1) X)))
      (x (V_- (V_* x x)))
      (y x)
      (z y)))))

(defthm
 Alternative-law-1-lemma-e
 (implies (and (Vp x)
    (Vp y))
     (equal (V_+ (V_- (V_* X (V_* X Y)))
           (S_* (* 2 (V_DOT (V_1) X))
          (V_* X Y)))
      (V_+ (V_- (V_* (V_* x x) y))
           (S_* (* 2 (V_DOT (V_1) X)) 
          (V_* x y)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)
             Alternative-law-1-lemma-a
             Alternative-law-1-lemma-c
             INVERSE-LAW-LEFT-2)
     :use Alternative-law-1-lemma-a)))

(defthm
 V_+-algebra-1
 (implies (and (Vp x)
    (Vp y))
    (equal (V_+ (V_+ x y)(V_- y))
     x)))

(defthm
 V_+-algebra-2
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (equal (V_+ x z)
       (V_+ y z))
      (equal x y)))
 :hints (("Goal"
     :in-theory (disable V_+-algebra-1
             COMMUTATIVITY-OF-V_+
             ASSOCIATIVITY-OF-V_+) 
     :use ((:instance
      V_+-algebra-1
      (y z))
     (:instance
      V_+-algebra-1
      (x y)
      (y z))))))

(defthm
 Alternative-law-1-lemma-f
 (implies (and (Vp x)
    (Vp y))
     (equal (V_- (V_* x (V_* x y)))
      (V_- (V_* (V_* x x) y))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             Alternative-law-1-lemma-e)
     :use Alternative-law-1-lemma-e)))

(defthm
 V_-algebra-1
 (implies (and (Vp x)
    (Vp y))
     (equal (equal (V_- x)(V_- y))
      (equal x y)))
 :hints (("Goal"
     :in-theory (disable V_-_V_-_X=X)
     :use (V_-_V_-_X=X
     (:instance
      V_-_V_-_X=X
      (x y))))))

(defthm
 Alternative-law-1
 (implies (and (Vp x)
    (Vp y))
     (equal (V_* x (V_* x y))
      (V_* (V_* x x) y)))
 :hints (("Goal" 
     :in-theory (disable Alternative-law-1-lemma-f)
     :use Alternative-law-1-lemma-f)))

(defthm
 Alternative-law-2-lemma-a
 (implies (and (Vp x)
    (Vp y))
     (equal (V_* (V_* y x)
           (V_conjugate x))
      (V_* y (V_* x 
            (V_conjugate x)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V_CONJUGATE)))))

(defthm
 Alternative-law-2-lemma-b
 (implies (and (Vp x)
    (Vp y))
     (equal (V_* (V_* y x)
           (V_conjugate x))
      (V_+ (V_- (V_* (V_* y x) x))
           (S_* (* 2 (V_DOT (V_1) x))
          (V_* y x)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             Left-Distributivity-V_*_V_+)
     :use (:instance
      Left-Distributivity-V_*_V_+
      (a 1)
      (b (* 2 (V_DOT (V_1) x)))
      (x (V_* y x))
      (y (V_- x))
      (z (V_1))))))

(defthm
 Alternative-law-2-lemma-c
 (implies (Vp x)
     (equal (V_* x (V_conjugate x))
      (V_+ (V_- (V_* x x))
           (S_* (* 2 (V_DOT (V_1) x)) x))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             Left-Distributivity-V_*_V_+)
     :use (:instance
      Left-Distributivity-V_*_V_+
      (a 1)
      (b (* 2 (V_DOT (V_1) x)))
      (y (V_- x))
      (z (V_1))))))

(defthm
 Alternative-law-2-lemma-d
 (implies (and (Vp x)
    (Vp y))
     (equal (V_* y
           (V_* x (V_conjugate x)))
      (V_+ (V_- (V_* y (V_* x x)))
           (S_* (* 2 (V_DOT (V_1) x)) 
          (V_* y x)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)
             Left-Distributivity-V_*_V_+)
     :use (:instance
      Left-Distributivity-V_*_V_+
      (a 1)
      (b (* 2 (V_DOT (V_1) x)))
      (x y)
      (y (V_- (V_* x x)))
      (z x)))))

(defthm
 Alternative-law-2-lemma-e
 (implies (and (Vp x)
    (Vp y))
     (equal (V_+ (V_- (V_* (V_* y x) x))
           (S_* (* 2 (V_DOT (V_1) x))
          (V_* y x)))
      (V_+ (V_- (V_* y (V_* x x)))
           (S_* (* 2 (V_DOT (V_1) x)) 
          (V_* y x)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_CONJUGATE)
             Alternative-law-2-lemma-a
             Alternative-law-2-lemma-c
             V_+-ALGEBRA-2
             V_-ALGEBRA-1
             INVERSE-LAW-right-2)
     :use Alternative-law-2-lemma-a)))

(defthm
 Alternative-law-2
 (implies (and (Vp x)
    (Vp y))
     (equal (V_* (V_* y x) x)
      (V_* y (V_* x x))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             Alternative-law-2-lemma-e)
     :use Alternative-law-2-lemma-e)))

(defthmD
 Moufang-law-lemma-a
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot u (V_* (V_* x y)
        (V_* z x)))
      (V_dot (V_* x y)
       (V_* u
            (V_* (V_conjugate x)
           (V_Conjugate z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_conjugate)
             Braid-Law-2)
    :use (:instance
    Braid-Law-2
    (x (V_* x y))
    (y (V_* z x))
    (z u)))))

(defthmD
 Moufang-law-lemma-b
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot (V_* x y)
       (V_* u
            (V_* (V_conjugate x)
           (V_Conjugate z))))
      (- (* 2 
      (V_dot u x)
      (V_dot y (V_* (V_conjugate x)
              (V_Conjugate z))))
         (V_dot (V_* u y)
          (V_* x
         (V_* (V_conjugate x)
              (V_Conjugate z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_conjugate)
             Braid-Law-1
             Braid-Law-2
             Exchange-Law)
     :use (:instance
     Exchange-Law
     (y (V_* (V_conjugate x)
       (V_Conjugate z)))
     (z y)))))

(defthmD
 Moufang-law-lemma-c
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (- (* 2 
      (V_dot u x)
      (V_dot y (V_* (V_conjugate x)
              (V_Conjugate z))))
         (V_dot (V_* u y)
          (V_* x
         (V_* (V_conjugate x)
              (V_Conjugate z)))))
      (- (* 2 
      (V_dot u x)
      (V_dot (V_* y z)
             (V_conjugate x)))
         (V_dot (V_* (v_conjugate x)
         (V_* u y))
          (V_* (V_conjugate x)
         (V_Conjugate z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_conjugate)
             Braid-Law-2
             Braid-Law-1)
     :use ((:instance
      Braid-Law-2
      (x y)
      (y z)
      (z (v_conjugate x)))
     (:instance
      Braid-Law-1
      (y (V_* (V_conjugate x)(V_conjugate z)))
      (z (V_* u y)))))))

(defthmD
 Moufang-law-lemma-d
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (- (* 2 
      (V_dot u x)
      (V_dot (V_* y z)
             (V_conjugate x)))
         (V_dot (V_* (v_conjugate x)
         (V_* u y))
          (V_* (V_conjugate x)
         (V_Conjugate z))))
      (- (* 2 
      (V_dot u x)
      (V_dot (V_* y z)
             (V_conjugate x)))
         (* (V_norm x)
      (V_dot (V_* u y)
             (V_Conjugate z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_conjugate)
             Braid-Law-1
             Braid-Law-2))))

(defthmD
 Moufang-law-lemma-e
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (- (* 2 
      (V_dot u x)
      (V_dot (V_* y z)
             (V_conjugate x)))
         (* (V_norm (V_conjugate x))
      (V_dot (V_* u y)
             (V_Conjugate z))))
      (- (* 2 
      (V_dot u x)
      (V_dot (V_* y z)
             (V_conjugate x)))
         (* (V_norm x)
      (V_dot u
             (V_* (V_conjugate z)
            (V_conjugate y)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_conjugate)
             Braid-Law-1
             Braid-Law-2)
     :use (:instance
     Braid-Law-2
     (x u)
     (z (V_conjugate z))))))

(defthm
 V_dot-x-V_conj-y=V_dot-y-V_conj-x
 (implies (and (Vp x)
    (Vp y))
     (equal (V_dot x (V_conjugate y))
      (V_dot y (V_conjugate x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_conjugate)
             Braid-Law-1
             Braid-Law-2)
    :use ((:instance 
     Braid-Law-1
     (z (V_1)))
    (:instance
     Braid-Law-2
     (z (V_1)))))))

(defthmD
 Moufang-law-lemma-f
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (- (* 2 
      (V_dot u x)
      (V_dot (V_* y z)
             (V_conjugate x)))
         (* (V_norm x)
      (V_dot u
             (V_* (V_conjugate z)
            (V_conjugate y)))))
      (- (* 2 
      (V_dot u x)
      (V_dot x
             (v_conjugate (V_* y z))))
         (* (V_norm x)
      (V_dot u
             (V_conjugate (V_* y z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_conjugate)))))

(defthmD
 Moufang-law-lemma-g
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot u (V_* (V_* x y)
        (V_* z x)))
      (- (* 2 
      (V_dot u x)
      (V_dot x
             (V_conjugate (V_* y z))))
         (* (V_norm x)
      (V_dot u
             (V_conjugate (V_* y z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_conjugate)
             PRODUCT-CONJUGATION
             Braid-Law-2
             V_DOT-X-V_CONJ-Y=V_DOT-Y-V_CONJ-X)
     :use (Moufang-law-lemma-a
     Moufang-law-lemma-b
     Moufang-law-lemma-c
     Moufang-law-lemma-d
     Moufang-law-lemma-e
     Moufang-law-lemma-f))))

(defthmD
 Moufang-law-lemma-h
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (- (* 2 
      (V_dot u x)
      (V_dot x
             (v_conjugate (V_* y z))))
         (* (V_norm x)
      (V_dot u
             (V_conjugate (V_* y z)))))
      (V_dot u 
       (V_+ (S_* (* 2
              (V_dot x
               (V_conjugate (V_* y z))))
           x)
            (S_* (- (V_norm x))
           (V_conjugate (V_* y z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_conjugate)
             PRODUCT-CONJUGATION
             Distributivity-V_dot-V_+-right)
     :use (:instance
     Distributivity-V_dot-V_+-right
     (x u)
     (a (* 2
           (V_dot x
            (v_conjugate (V_* y z)))))
     (y x)
     (b (- (V_norm x)))
     (z (V_conjugate (V_* y z)))))))

(defthm
 Moufang-law-lemma-i
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot u (V_* (V_* x y)
        (V_* z x))) 
      (V_dot u 
       (V_+ (S_* (* 2
              (V_dot x
               (V_conjugate (V_* y z))))
           x)
            (S_* (- (V_norm x))
           (V_conjugate (V_* y z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_conjugate)
             PRODUCT-CONJUGATION)
     :use (Moufang-law-lemma-g
     Moufang-law-lemma-h))))

(defthmD
 Moufang-law-lemma-j
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_* (V_* x y)
           (V_* z x)) 
      (V_+ (S_* (* 2
             (V_dot x
              (V_conjugate (V_* y z))))
          x)
           (S_* (- (V_norm x))
          (V_conjugate (V_* y z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_conjugate)
             PRODUCT-CONJUGATION)
     :use (:instance
     Forall-u-V_dot-u-x=V_dot-u-y->x=y
     (x (V_* (V_* x y)
       (V_* z x)))
     (y (V_+ (S_* (* 2
         (V_dot x
          (V_conjugate (V_* y z))))
            x)
       (S_* (- (V_norm x))
            (V_conjugate (V_* y z)))))))))

(in-theory (disable Moufang-law-lemma-i))

(defthm
 Moufang-law-1
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_* (V_* x y)
           (V_* z x))
      (V_* x 
           (V_* (V_* y z)
          x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_conjugate)
             PRODUCT-CONJUGATION)
     :use (Moufang-law-lemma-j
     (:instance
      Moufang-law-lemma-j
      (y (V_1))
      (z (V_* y z)))))))

(defthm
 Moufang-law-2
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_* (V_* x 
          (V_* y z))
           x)
      (V_* x 
           (V_* (V_* y z)
          x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             (:DEFINITION V_conjugate)
             PRODUCT-CONJUGATION)
     :use (Moufang-law-lemma-j
     (:instance
      Moufang-law-lemma-j
      (z (V_1))
      (y (V_* y z)))))))

(defthm
 Alternative-law-3
 (implies (and (Vp x)
    (Vp y))
     (equal (V_* (V_* x y) x)
      (V_* x (V_* y x))))
 :hints (("Goal" 
     :in-theory (disable Moufang-law-2)
     :use (:instance
     Moufang-law-2
     (z (V_1))))))

#|================================
 Construct a composition algrebra 
   out of the cons pairs of elements of V:
==========================|#

(defun
 V2p (x)
 (and (consp x)
      (Vp (car x))
      (Vp (cdr x))))

(defun
 V2_0 () 
 (cons (V_0)(V_0)))

(defun
 V2_+ (x y) 
 (cons (V_+ (car x)(car y))
  (V_+ (cdr x)(cdr y))))

(defun
 V2_- (x)
 (cons (V_- (car x))
  (V_- (cdr x))))

(defun
 S2_* (a x)
 (cons (S_* a (car x))
  (S_* a (cdr x))))

(defthm  
 V2_Vector-closure
 (and (V2p (V2_0))
      (implies (and (V2p x)
         (V2p y))
    (V2p (V2_+ x y)))
      (implies (V2p x)
    (V2p (V2_- x)))
      (implies (and (real/rationalp a)
         (V2p x))
    (V2p (S2_* a x)))))

(defthm
 Associativity-of-V2_+
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_+ (V2_+ x y) z)
      (V2_+ x (V2_+ y z)))))

(defthm
 Commutativity-of-V2_+
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_+ x y)
      (V2_+ y x))))

(defthm
 Unicity-of-V2_0
 (implies (V2p x)
     (equal (V2_+ (V2_0) x)
      x)))

(defthm
 Inverse-of-V2_+
 (implies (V2p x)
     (equal (V2_+ x (V2_- x))
      (V2_0))))

(defthm
 Associativity-of-S2_*
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (V2p x))
     (equal (S2_* a (S2_* b x))
      (S2_* (* a b) x))))

(defthm
 V2-Unicity-of-Scalar-1
 (implies (V2p x)
     (equal (S2_* 1 x) x)))

(defthm
 Distributivity-S2_*-scalar-+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (V2p x))
     (equal (S2_* (+ a b) x)
      (V2_+ (S2_* a x)(S2_* b x)))))

(defthm
 Distributivity-S2_*-V2_+
 (implies (and (real/rationalp a)
    (V2p x)
    (V2p y))
     (equal (S2_* a (V2_+ x y))
      (V2_+ (S2_* a x)(S2_* a y)))))

(defun
 V2_* (x y)
 (cons (V_+ (V_* (car x)
      (car y))
       (V_- (V_* (V_conjugate (cdr y))
           (cdr x))))
  (V_+ (V_* (cdr y) 
      (car x))
       (V_* (cdr x)
      (V_conjugate (car y))))))

(defun
 V2_1 () 
 (cons (V_1)(V_0)))

(defthm
 V2_1&V2_*-closure
 (and (V2p (V2_1))
      (implies (and (V2p x)
         (V2p y))
    (V2p (V2_* x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)))))

(defthm
 Not-V2_1=V2_0
 (not (equal (V2_1)(V2_0))))

(defthm
 V_conjugate-S_*=S_*-V_conjugate
 (implies (and (real/rationalp a)
    (Vp x))
     (equal (V_conjugate (S_* a x))
      (S_* a (V_conjugate x))))
 :hints (("Goal"
     :in-theory (disable Realp>=0-V_norm)
     :use (Realp>=0-V_norm
     (:instance
      Realp>=0-V_norm
      (x (V_+ (V_1) x)))))))

(defthm
 Left-Distributivity-V2_*_V2_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_* x 
      (V2_+ (S2_* a y)
            (S2_* b z)))
      (V2_+ (S2_* a
            (V2_* x y))
      (S2_* b
            (V2_* x z)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)))))

(defthm
 Right-Distributivity-V2_*_V2_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_* (V2_+ (S2_* a x)
            (S2_* b y))
      z)
      (V2_+ (S2_* a
            (V2_* x z))
      (S2_* b
            (V2_* y z)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)))))

(defthm
 V_-V_0=V_0
 (equal (V_- (V_0))
   (V_0))
 :hints (("Goal"
     :in-theory (disable S_*-V_0=V_0)
     :use (:instance
     S_*-V_0=V_0
     (a -1)))))

(defthm
 Unicity-of-V2_1
 (implies (V2p x)
     (and (equal (V2_* (V2_1) x) x)
    (equal (V2_* x (V2_1)) x)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)))))

(defun
 V2_norm (x)
 (+ (V_norm (car x))
    (V_norm (cdr x))))

(defthm
 Realp>=0-V2_norm
 (implies (V2p x)
     (and (real/rationalp (V2_norm x))
    (>= (V2_norm x) 0)))
 :hints (("Goal"
     :in-theory (disable Realp>=0-V_norm)
     :use ((:instance
      Realp>=0-V_norm
      (x (car x)))
     (:instance
      Realp>=0-V_norm
      (x (cdr x)))))))

(defthm
 V2_norm=0
 (implies (V2p x)
     (equal (equal (V2_norm x) 0)
      (equal x (V2_0))))
 :hints (("Goal"
     :in-theory (disable Realp>=0-V_norm)
     :use ((:instance
      Realp>=0-V_norm
      (x (car x)))
     (:instance
      Realp>=0-V_norm
      (x (cdr x)))))))

(defthmD
 V2-Composition-Law-lemma-a
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot u
       (V_* (V_* x y) z))
      (V_dot u
       (V_* x (V_* y z)))))
 :hints (("Goal"
     :in-theory (e/d (V_*-associativity)
         ((:DEFINITION V_DOT-DEF))))))

(defthmD
 V2-Composition-Law-lemma-b
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_dot (V_* x y)
       (V_* u (V_conjugate z)))
      (V_dot (V_* y z)  
       (V_* (V_conjugate x) u))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)
             (:DEFINITION V_DOT-DEF))
     :use V2-Composition-Law-lemma-a)))

(defthmD
 V2-Composition-Law-lemma-c
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (+ (V_norm (V_* y z))
         (- (* 2 (V_dot (V_* y z)  
            (V_* (V_conjugate x) u))))
         (V_norm (V_* (V_conjugate x) u))
         (V_norm (V_* x y))
         (* 2 (V_dot (V_* x y)
         (V_* u (V_conjugate z))))
         (V_norm (V_* u (V_conjugate z))))
      (+ (* (V_norm y)
      (V_norm z))
         (* (V_norm y)
      (V_norm x))
         (* (V_norm u)
      (V_norm z))
         (* (V_norm u)
      (V_norm x)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)
             (:DEFINITION V_DOT-DEF)
             BRAID-LAW-1
             BRAID-LAW-2)
     :use V2-Composition-Law-lemma-b)))

(defthm
 V_norm-V_+=
 (implies (and (Vp x)
    (Vp y))
     (equal (V_norm (V_+ x y))
      (+ (V_norm x)
         (* 2 (V_dot x y))
         (V_norm y))))
 :hints (("Goal"
     :in-theory (disable Realp>=0-V_norm)
     :use ((:instance
      Realp>=0-V_norm
      (x (V_+ x y)))))))

(defthmD
 V_norm-V_-=V_norm-lemma-a
 (implies (Vp x)
     (equal (V_norm (V_* (V_- x)
             (V_- x)))
      (V_norm (V_* x x)))))

(defthmD
 V_norm-V_-=V_norm-lemma-b
 (implies (Vp x)
     (equal (* (V_norm (V_- x))
         (V_norm (V_- x)))
      (* (V_norm x)
         (V_norm x))))
 :hints (("Goal"
     :in-theory (disable V_*-V_-=V_-V_*-LEFT
             V_*-V_-=V_-V_*-RIGHT)
     :use V_norm-V_-=V_norm-lemma-a)))

(defthmD
 V_norm-V_-=V_norm-lemma-c
 (implies (and (real/rationalp a)
    (real/rationalp b))
     (equal (equal a b)
      (equal (- a b) 0))))

(defthmD
 V_norm-V_-=V_norm-lemma-d
 (implies (and (real/rationalp a)
    (>= a 0)
    (real/rationalp b)
    (>= b 0))
     (equal (equal (* a a)(* b b))
      (equal a b)))
 :hints (("Goal"
     :in-theory (disable INVERSE-OF-+-AS=0)
     :use ((:instance
      V_norm-V_-=V_norm-lemma-c
      (a (* a a))
      (b (* b b)))
     (:theorem
      (equal (- (* a a)(* b b))
       (* (+ a b)(- a b))))))))

(defthm
 V_norm-V_-=V_norm
 (implies (Vp x)
     (equal (V_norm (V_- x))
      (V_norm x)))
 :hints (("Goal"
     :use (V_norm-V_-=V_norm-lemma-b
     (:instance
      V_norm-V_-=V_norm-lemma-d
      (a (V_norm (V_- x)))
      (b (V_norm x)))))))

(defthmD
 V2-Composition-Law-lemma-d
 (implies (and (Vp u)
    (Vp x)
    (Vp y)
    (Vp z))
     (equal (+ (V_norm (V_+ (V_* y z)
          (V_- (V_* (V_conjugate x) u))))
         (V_norm (V_+ (V_* x y)
          (V_* u (V_conjugate z)))))
      (* (+ (V_norm y)
      (V_norm u))
         (+ (v_norm z)
      (V_norm x)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)
             (:DEFINITION V_DOT-DEF)
             BRAID-LAW-1
             BRAID-LAW-2)
     :use V2-Composition-Law-lemma-c)))

(defthm
 V2-Composition-Law
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_norm (V2_* x y))
      (* (V2_norm x)
         (V2_norm y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)
             V_NORM-V_+=)
     :use (:instance 
     V2-Composition-Law-lemma-d
     (u (cdr x))
     (x (cdr y))
     (y (car x))
     (z (car y))))))

(defun
 V2_dot (x y)
 (+ (V_dot (car x)(car y))
    (V_dot (cdr x)(cdr y))))

(defthmD
 V2_dot-def
 (equal (V2_dot x y)
   (* 1/2 (+ (V2_norm (V2_+ x y))
       (- (V2_norm x))
       (- (V2_norm y)))))
  :rule-classes :definition)

(defthm
 Distributivity-V2_dot-V2_+
  (implies (and (real/rationalp a)
     (real/rationalp b)
     (V2p x)
     (V2p y)
     (V2p z))
      (equal (V2_dot (V2_+ (S2_* a x)
         (S2_* b y))
         z)
       (+ (* a (V2_dot x z))
          (* b (V2_dot y z))))))

(defun-sk 
 Forall-u-V2_dot-u-x=0 (x)
 (forall (u)
    (implies (V2p u)
       (equal (V2_dot u x) 0)))
   :rewrite :direct)

;; Here are the definition of Forall-u-V2_dot-u-x=0
;;           and the theorem: Forall-u-V2_dot-u-x=0-necc:

;; In addition to FORALL-U-V2_DOT-U-X=0-WITNESS, we export 
;; FORALL-U-V2_DOT-U-X=0.

;; The following constraint is associated with both of the functions 
;; FORALL-U-V2_DOT-U-X=0 and FORALL-U-V2_DOT-U-X=0-WITNESS:

;; (AND (EQUAL (FORALL-U-V2_DOT-U-X=0 X)
;;             (LET ((U (FORALL-U-V2_DOT-U-X=0-WITNESS X)))
;;                  (IMPLIES (V2P U)
;;                           (EQUAL (V2_DOT U X) 0))))
;;      (IMPLIES (FORALL-U-V2_DOT-U-X=0 X)
;;               (IMPLIES (V2P U)
;;                        (EQUAL (V2_DOT U X) 0))))

(defthm
 V_dot-V_1-V_1=1
 (equal (V_dot (V_1)(V_1)) 1)
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             V_NORM-V_+=)
     :use (:instance
     V_NORM-V_+=
     (x (V_1))
     (y (V_- (V_1)))))))

(defthmD
 V_dot-x-x=V_norm-x
 (implies (Vp x)
     (equal (V_dot x x)
      (V_norm x)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             Scaling-law-left
             Realp>=0-V_norm)
     :use ((:instance
      Scaling-law-left
      (y (V_1))
      (z (V_1)))
     Realp>=0-V_norm))))

(defthm
  Realp>=0-V_dot-x-x
  (implies (Vp x)
      (and (real/rationalp (V_dot x x))
     (>= (V_dot x x) 0)))
  :hints (("Goal"
      :in-theory (disable (:DEFINITION V_DOT-DEF))
      :use V_dot-x-x=V_norm-x)))

(defthm
 V_dot-x-x=0
 (implies (Vp x)
     (equal (equal (V_dot x x) 0)
      (equal x (V_0))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF))
     :use V_dot-x-x=V_norm-x)))

(defthm
 V2_dot-x-x=0
 (implies (V2p x)
     (equal (equal (V2_dot x x) 0)
      (equal x (V2_0))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)
             Realp>=0-V_dot-x-x
             REALP-V_DOT)
     :use ((:instance
      Realp>=0-V_dot-x-x
      (x (car x)))
     (:instance
      Realp>=0-V_dot-x-x
      (x (cdr x)))))))

(defthm  ;;V2_dot is nonsingular
 Forall-u-V2_dot-u-x=0->x=V2_0
 (implies (and (V2p x)
    (Forall-u-V2_dot-u-x=0 x))
     (equal x (V2_0)))
 :rule-classes nil
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P)
             (:DEFINITION V2_0)
             V2_dot-x-x=0)
     :use V2_dot-x-x=0)))

(defun
 V2_conjugate (x)
 (cons (V_conjugate (car x))
  (V_- (cdr x))))

(defthm
 V2p-V2_conjugate
 (implies (V2p x)
     (V2p (V2_conjugate x)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)))))

(defthmD
 V2_conjugate-def-rewrite
 (implies (V2p x)
     (equal (V2_conjugate x)
      (V2_+ (S2_* (* 2 (V2_dot x (V2_1)))
            (V2_1))
      (V2_- x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_DOT-DEF)))))

(defthmD
 V2_*-cons=cons-V_*
 (implies (and (Vp x)
    (Vp y))
     (equal (V2_* (cons x (V_0))
      (cons y (V_0)))
      (cons (V_* x y)(V_0))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)))))

(defthmD
 V2_norm=V_norm
 (implies (Vp x)
     (and (equal (V2_norm (cons x (V_0)))
           (V_norm x))
    (equal (V2_norm (cons (V_0) x))
           (V_norm x))))
 :hints (("Goal"
     :in-theory (disable Realp>=0-V_norm)
     :use Realp>=0-V_norm)))

(defthmD  
 Vp-V_0-orthogonal-V_0-Vp
 (implies (and (Vp x)
    (Vp y))
     (equal (V2_dot (cons x (V_0))
        (cons (V_0) y))
      0)))

(defthmD
 Vp*i=cons-V_0-Vp
 (implies (Vp x)
     (equal (V2_* (cons x (V_0))
      (cons (V_0)(V_1)))
      (cons (V_0) x)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V_CONJUGATE)))))

;;================================

(defthm
 Commutativity-2-of-V_*
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_* x (V_* y z))
      (V_* y (V_* x z))))
 :hints (("Goal"
     :in-theory (enable V_*-associativity) 
     :use (:theorem
     (implies (and (Vp x)
             (Vp y)
             (Vp z))
        (equal (V_* (V_* x y) z)
         (V_* (V_* y x) z)))))
    ("Subgoal 1"
     :in-theory (enable V_*-commutativity))))

(defthm
 Distributivity-V_*_V_+
 (implies (and (Vp x)
    (Vp y)
    (Vp z))
     (equal (V_* x 
           (V_+ y z))
      (V_+ (V_* x y)
           (V_* x z))))
 :hints (("Goal"
     :in-theory (disable Left-Distributivity-V_*_V_+)
     :use (:instance
     Left-Distributivity-V_*_V_+
     (a 1)
     (b 1)))))

(defthm
 V_conjugate-V_-=V_-V_conjugate
 (implies (Vp x)
     (equal (V_conjugate (V_- x))
      (V_- (V_conjugate x))))
 :hints (("Goal"
     :in-theory (disable (:definition V_conjugate)
             V_CONJUGATE-S_*=S_*-V_CONJUGATE)
     :use (:instance
     V_CONJUGATE-S_*=S_*-V_CONJUGATE
     (a -1)))))

(defthm
 V2_*-associativity
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_* (V2_* x y) z)
      (V2_* x (V2_* y z))))
 :hints (("Goal"
     :in-theory (e/d (V_*-associativity
          V_*-commutativity)
         ((:DEFINITION V_CONJUGATE))))))