#|==========================================
 Cayley-Dickson Construction
   cayley5.lisp

  1 April 2017

 Start with a composition algebra V1.
 Let V2 be the set of cons pairs of elements from V1.
 If V2 is a commutative, associative composition algebra, 
    then V1_multiplication is associative and commutative,
    and V1_conjugation is trivial.

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
(certify-book "cayley5"
             0   ;; world with no commands
             nil ;;compile-flg  
             ) 
===============================
To use:
(include-book 
        "cayley5"  
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
    "cayley5.lisp")              ; read and evaluate each form in file 
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

(encapsulate    
(;; Two Real Composition Algebras:
 ;;  A Real Vector Algebra with Identity:
 ;;    A Real Vector Space with Multiplication
 ;;    and a Multiplicative Identity.
 ;;  The Vector Algebra also has a real valued Norm
 ;;    and a real valued Dot (or Inner) Product
 ;;    satisfying the Composition Law
 ;;        Norm(xy) = Norm(x)Norm(y).
 ;; ===============================
 ;; Real Vector Space Operations:
 ((V1p *)      => *)   ;; Predicate for set of vectors
 ((V2p *)      => *)   ;; Predicate for set of vectors
 ((V1_0)       => *)   ;; Zero vector
 ((V2_0)       => *)   ;; Zero vector
 ((V1_+ * *)   => *)   ;; Vector addition
 ((V2_+ * *)   => *)   ;; Vector addition
 ((V1_- *)     => *)   ;; Vector minus
 ((V2_- *)     => *)   ;; Vector minus
 ((S1_* * *)   => *)   ;; Scalar multiplication
 ((S2_* * *)   => *)   ;; Scalar multiplication
 ;; Vector Multiplication and Identity Operations:
 ((V1_* * *)   => *)   ;; Vector multiplication
 ((V2_* * *)   => *)   ;; Vector multiplication
 ((V1_1)       => *)   ;; One vector
 ((V2_1)       => *)   ;; One vector
 ;; Norm operation:
 ((V1_norm *)  => *)   ;; Vector Norm
 ((V2_norm *)  => *)   ;; Vector Norm
 ;; Dot (or Inner) Product Operation:
 ((V1_dot * *) => *)   ;; Vector Dot Product
 ((V2_dot * *) => *)   ;; Vector Dot Product
 ((Forall-u-V1_dot-u-x=0 *) => *)   ;; Predicate with quantifier
 ((Forall-u-V2_dot-u-x=0 *) => *)   ;; Predicate with quantifier
 ((Forall-u-V1_dot-u-x=0-witness *) => *)  ;; Skolem function 
 ((Forall-u-V2_dot-u-x=0-witness *) => *)) ;; Skolem function 

(local 
 (defun 
   V1p (x)
   (real/rationalp x)))

(local 
 (defun 
   V2p (x)
   (and (consp x)
   (real/rationalp (car x))
   (real/rationalp (cdr x)))))

(local
 (defun
   V1_0 ()
   0))

(local
 (defun
   V2_0 ()
   (cons 0 0)))

(local
 (defun
   V1_+ (x y)
   (+ x y)))

(local
 (defun
   V2_+ (x y)
   (cons (+ (car x)(car y))
    (+ (cdr x)(cdr y)))))

(local
 (defun
   V1_- (x)
   (- x)))

(local
 (defun
   V2_- (x)
   (cons (- (car x))
    (- (cdr x)))))

(local
 (defun
   S1_* (a x)
   (* a x)))

(local
 (defun
   S2_* (a x)
   (cons (* a (car x))
    (* a (cdr x)))))

;; Real Vector Space Axioms:
(defthm 
  V2p-def
  (equal (V2p x)
    (and (consp x)
         (V1p (car x))
         (V1p (cdr x))))
  :rule-classes :definition)

#|========================
(defthm
   V2_0-def 
   (equal (V2_0)
     (cons (V1_0)(V1_0)))
   :rule-classes :definition)
======|#

(defthm
  V2_+-def 
  (equal (V2_+ x y)
    (cons (V1_+ (car x)(car y))
    (V1_+ (cdr x)(cdr y))))
  :rule-classes :definition)

#|===================
(defthm
   V2_-_def
   (equal (V2_- x)
     (cons (V1_- (car x))
     (V1_- (cdr x))))
   :rule-classes :definition)
======|#

(defthm
   S2_*-def
   (equal (S2_* a x)
     (cons (S1_* a (car x))
     (S1_* a (cdr x))))
   :rule-classes :definition)

(defthm  
  Vector1-closure
  (and (V1p (V1_0))
  (implies (and (V1p x)
          (V1p y))
     (V1p (V1_+ x y)))
  (implies (V1p x)
     (V1p (V1_- x)))
  (implies (and (real/rationalp a)
          (V1p x))
     (V1p (S1_* a x)))))

(defthm  
  Vector2-closure-V2_0-V2_-
  (and (V2p (V2_0))
  (implies (V2p x)
     (V2p (V2_- x)))))

(defthm
  Associativity-of-V1_+
  (implies (and (V1p x)
     (V1p y)
     (V1p z))
      (equal (V1_+ (V1_+ x y) z)
       (V1_+ x (V1_+ y z)))))

(defthm
  Commutativity-of-V1_+
  (implies (and (V1p x)
     (V1p y))
      (equal (V1_+ x y)
       (V1_+ y x))))

(defthm
  Unicity-of-V1_0
  (implies (V1p x)
      (equal (V1_+ (V1_0) x)
       x)))

(defthm
  Unicity-of-V2_0
  (implies (V2p x)
      (equal (V2_+ (V2_0) x)
       x)))

(defthm
  Inverse-of-V1_+
  (implies (V1p x)
      (equal (V1_+ x (V1_- x))
       (V1_0))))

(defthm
  Inverse-of-V2_+
  (implies (V2p x)
      (equal (V2_+ x (V2_- x))
       (V2_0))))

(defthm
  Associativity-of-S1_*
  (implies (and (real/rationalp a)
     (real/rationalp b)
     (V1p x))
      (equal (S1_* a (S1_* b x))
       (S1_* (* a b) x))))

(defthm
  Unicity-of-S1-Scalar-1
  (implies (V1p x)
      (equal (S1_* 1 x) x)))

(defthm
  Distributivity-S1_*-scalar-+
  (implies (and (real/rationalp a)
     (real/rationalp b)
     (V1p x))
      (equal (S1_* (+ a b) x)
       (V1_+ (S1_* a x)(S1_* b x)))))

(defthm
  Distributivity-S1_*-V1_+
  (implies (and (real/rationalp a)
     (V1p x)
     (V1p y))
      (equal (S1_* a (V1_+ x y))
       (V1_+ (S1_* a x)(S1_* a y)))))

(local
 (defun
   V1_* (x y)
   (* x y)))

(local
 (defun
   V2_* (x y)
   (cons (+ (* (car x)(car y))
       (- (* (cdr x)(cdr y))))
    (+ (* (car x)(cdr y))
       (* (cdr x)(car y))))))

(local
 (defun
   V1_1 ()
   1))

(local
 (defun
   V2_1 ()
   (cons 1 0)))

;; Additional Real Vector Algebra Axioms:
(defthm
  V1_1&V1_*-closure
  (and (V1p (V1_1))
  (implies (and (V1p x)
          (V1p y))
     (V1p (V1_* x y)))))

(defthm 
  V2_1&V2_*-closure
  (and (V2p (V2_1))
  (implies (and (V2p x)
          (V2p y))
     (V2p (V2_* x y)))))

(defthm
  Not-V1_1=V1_0
  (not (equal (V1_1)(V1_0))))

(defthm
  Not-V2_1=V2_0
  (not (equal (V2_1)(V2_0))))

(defthm
  Left-Distributivity-V1_*_V1_+
  (implies (and (real/rationalp a)
     (real/rationalp b)
     (V1p x)
     (V1p y)
     (V1p z))
      (equal (V1_* x 
       (V1_+ (S1_* a y)
             (S1_* b z)))
       (V1_+ (S1_* a
             (V1_* x y))
       (S1_* b
             (V1_* x z))))))

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
             (V2_* x z))))))

(defthm
  Right-Distributivity-V1_*_V1_+
  (implies (and (real/rationalp a)
     (real/rationalp b)
     (V1p x)
     (V1p y)
     (V1p z))
      (equal (V1_* (V1_+ (S1_* a x)
             (S1_* b y))
       z)
       (V1_+ (S1_* a
             (V1_* x z))
       (S1_* b
             (V1_* y z))))))

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
             (V2_* y z))))))

(defthm
  Unicity-of-V1_1
  (implies (V1p x)
      (and (equal (V1_* (V1_1) x) x)
     (equal (V1_* x (V1_1)) x))))

(defthm
  Unicity-of-V2_1
  (implies (V2p x)
      (and (equal (V2_* (V2_1) x) x)
     (equal (V2_* x (V2_1)) x))))

(defthmD
  V2_*-cons=cons-V1_*
  (implies (and (V1p x)
     (V1p y))
      (equal (V2_* (cons x (V1_0))
       (cons y (V1_0)))
       (cons (V1_* x y)(V1_0)))))

(local
 (defun
   V1_norm (x)
   (* x x)))

(local
 (defun
   V2_norm (x)
   (+ (* (car x)(car x))
      (* (cdr x)(cdr x)))))

;; Additional Vector Norm and Dot Product Axioms:
(defthm
  Realp>=0-V1_norm
  (implies (V1p x)
      (and (real/rationalp (V1_norm x))
     (>= (V1_norm x) 0))))

(defthm
  Realp>=0-V2_norm
  (implies (V2p x)
      (and (real/rationalp (V2_norm x))
     (>= (V2_norm x) 0))))

(defthm
  V1_norm=0
  (implies (V1p x)
      (equal (equal (V1_norm x) 0)
       (equal x (V1_0)))))

(defthm
  V2_norm=0
  (implies (V2p x)
      (equal (equal (V2_norm x) 0)
       (equal x (V2_0)))))

(defthm
  V1-Composition-Law
  (implies (and (V1p x)
     (V1p y))
      (equal (V1_norm (V1_* x y))
       (* (V1_norm x)
          (V1_norm y)))))

(defthm
  V2-Composition-Law
  (implies (and (V2p x)
     (V2p y))
      (equal (V2_norm (V2_* x y))
       (* (V2_norm x)
          (V2_norm y)))))

(defthm
  V2_norm=V1_norm
  (implies (V1p x)
      (and (equal (V2_norm (cons x (V1_0)))
      (V1_norm x))
     (equal (V2_norm (cons (V1_0) x))
      (V1_norm x)))))

(local
 (defun
   V1_dot (x y)
   (* 1/2 (+ (V1_norm (V1_+ x y))
        (- (V1_norm x))
        (- (V1_norm y))))))

(local
 (defun
   V2_dot (x y)
   (* 1/2 (+ (V2_norm (V2_+ x y))
        (- (V2_norm x))
        (- (V2_norm y))))))

(defthm
  V1_dot-def
  (equal (V1_dot x y)
    (* 1/2 (+ (V1_norm (V1_+ x y))
        (- (V1_norm x))
        (- (V1_norm y)))))
  :rule-classes :definition)

(defthm
  V2_dot-def
  (equal (V2_dot x y)
    (* 1/2 (+ (V2_norm (V2_+ x y))
        (- (V2_norm x))
        (- (V2_norm y)))))
  :rule-classes :definition)

(defthm
  Distributivity-V1_dot-V1_+
  (implies (and (real/rationalp a)
     (real/rationalp b)
     (V1p x)
     (V1p y)
     (V1p z))
      (equal (V1_dot (V1_+ (S1_* a x)
         (S1_* b y))
         z)
       (+ (* a (V1_dot x z))
          (* b (V1_dot y z))))))

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

(local
 (defthm
   V1_dot=0
   (implies (V1p x)
       (equal (equal (V1_dot x x) 0)
        (equal x (V1_0))))))

(local
 (defthm
   V2_dot=0
   (implies (V2p x)
       (equal (equal (V2_dot x x) 0)
        (equal x (V2_0))))))

(local
 (defun-sk 
   Forall-u-V1_dot-u-x=0 (x)
   (forall (u)
      (implies (V1p u)
         (equal (V1_dot u x) 0)))
   :rewrite :direct))

(local
 (defun-sk 
   Forall-u-V2_dot-u-x=0 (x)
   (forall (u)
      (implies (V2p u)
         (equal (V2_dot u x) 0)))
   :rewrite :direct))

(defthm
  Forall-u-V1_dot-u-x=0-def
  (equal (Forall-u-V1_dot-u-x=0 x)
    (let ((u (Forall-u-V1_dot-u-x=0-witness x)))
         (implies (V1p u)
      (equal (V1_dot u x) 0))))
  :rule-classes :definition)

(defthm
  Forall-u-V2_dot-u-x=0-def
  (equal (Forall-u-V2_dot-u-x=0 x)
    (let ((u (Forall-u-V2_dot-u-x=0-witness x)))
         (implies (V2p u)
      (equal (V2_dot u x) 0))))
  :rule-classes :definition)

(defthm
  Forall-u-V1_dot-u-x=0-necc
  (implies (Forall-u-V1_dot-u-x=0 x)
      (implies (V1p u)
         (equal (V1_dot u x) 0))))

(defthm
  Forall-u-V2_dot-u-x=0-necc
  (implies (Forall-u-V2_dot-u-x=0 x)
      (implies (V2p u)
         (equal (V2_dot u x) 0))))

(defthm  ;;V1_dot is nonsingular
  Forall-u-V1_dot-u-x=0->x=V1_0
  (implies (and (V1p x)
     (Forall-u-V1_dot-u-x=0 x))
      (equal x (V1_0)))
  :rule-classes nil
  :hints (("Goal"
      :in-theory (disable V1_dot=0)
      :use V1_dot=0)))

(defthm  ;;V2_dot is nonsingular
  Forall-u-V2_dot-u-x=0->x=V2_0
  (implies (and (V2p x)
     (Forall-u-V2_dot-u-x=0 x))
      (equal x (V2_0)))
  :rule-classes nil
  :hints (("Goal"
      :in-theory (disable V2_dot=0)
      :use V2_dot=0)))

#|=======================================
(defthm  
  V1_0-V1_1-orthogonal-V1p-V1_0
  (implies (V1p x)
      (equal (V2_dot (cons (V1_0)(V1_1))
         (cons x (V1_0)))
       0)))
====================|#

(defthm  
  V1p-V1_0-orthogonal-V1_0-V1p
  (implies (and (V1p x)
     (V1p y))
      (equal (V2_dot (cons x (V1_0))
         (cons (V1_0) y))
       0)))

(defthmD
   V2_1-def 
   (equal (V2_1)
     (cons (V1_1)(V1_0)))
   :rule-classes :definition)

(defthmD
  V1p*i=cons-V1_0-V1p
  (implies (V1p x)
      (equal (V2_* (cons x (V1_0))
       (cons (V1_0)(V1_1)))
       (cons (V1_0) x))))

#|=============================
(defthm
  V2_1-orthogonal-V1_0-V1p
  (implies (V1p x)
      (equal (V2_dot (V2_1) (cons (V1_0) x))
       0)))
==================|#
;; need (V_dot x x) >= 0 and (V_dot x x) = 0 iff x = (V_0)
;;    no longer needed -- use V_dot is nonsingular.

(defthmD
  V2_*-associativity
  (implies (and (V2p x)
     (V2p y)
     (V2p z))
     (equal (V2_* (V2_* x y) z)
      (V2_* x (V2_* y z)))))

(defthmD
  V2_*-commutativity
  (implies (and (V2p x)
     (V2p y))
      (equal (V2_* x y)
       (V2_* y x))))

) ;; end encapsulate

;;====================================
;; These next few theorems show that 
;;  V2 satisfies the same axioms as V1.

(defthm  
 Vector2-closure-V2_+_S2_*
 (and (implies (and (V2p x)
         (V2p y))
    (V2p (V2_+ x y)))
      (implies (and (real/rationalp a)
         (V2p x))
    (V2p (S2_* a x)))))

(defthm 
 Associativity-of-V2_+
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_+ (V2_+ x y) z)
      (V2_+ x (V2_+ y z))))
 :hints (("Goal"
     :in-theory (disable COMMUTATIVITY-OF-V1_+))))

(defthm
 Commutativity-of-V2_+
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_+ x y)
      (V2_+ y x))))

#|======================
(defthm 
 Unicity-of-V2_0
 (implies (V2p x)
     (equal (V2_+ (V2_0) x)
      x)))
======|#
#|================
(defthm
 Inverse-of-V2_+
 (implies (V2p x)
     (equal (V2_+ x (V2_- x))
      (V2_0))))
======|#

(defthm 
 Associativity-of-S2_*
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (V2p x))
     (equal (S2_* a (S2_* b x))
      (S2_* (* a b) x))))

(defthm
 Unicity-of-S2-Scalar-1
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
;;===================================

;; (invisible-fns-table (w state))
(add-invisible-fns V1_+ V1_-)
(add-invisible-fns V1_- V1_-)
(add-invisible-fns V2_+ V2_-)
(add-invisible-fns V2_- V2_-)
;; (invisible-fns-table (w state))

;; Real Vector Space Theorems:
(defthm
 Commutativity-2-of-V1_+
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_+ x (V1_+ y z))
      (V1_+ y (V1_+ x z))))
 :hints (("Goal"
     :in-theory (disable Commutativity-of-V1_+) 
     :use (:theorem
     (implies (and (V1p x)
             (V1p y)
             (V1p z))
        (equal (V1_+ (V1_+ x y) z)
         (V1_+ (V1_+ y x) z)))))
    ("Subgoal 1"
     :in-theory (enable Commutativity-of-V1_+))))

(defthm
 Commutativity-2-of-V2_+
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_+ x (V2_+ y z))
      (V2_+ y (V2_+ x z))))
 :hints (("Goal"
     :in-theory (disable Commutativity-of-V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF))
     :use (:theorem
     (implies (and (V2p x)
             (V2p y)
             (V2p z))
        (equal (V2_+ (V2_+ x y) z)
         (V2_+ (V2_+ y x) z)))))
    ("Subgoal 1"
     :in-theory (e/d (Commutativity-of-V2_+)
         ((:DEFINITION V2P-DEF)
          (:DEFINITION V2_+-DEF))))))

(defthm
 V1_-_cancellation-on-right
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_+ x (V1_+ y (V1_- x))) y)) 
 :hints (("Goal"
     :in-theory (disable Commutativity-2-of-V1_+)
     :use (:instance
     Commutativity-2-of-V1_+
     (z (V1_- x))))))

(defthm
 V2_-_cancellation-on-right
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_+ x (V2_+ y (V2_- x))) y)) 
 :hints (("Goal"
     :in-theory (disable Commutativity-2-of-V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF))
     :use (:instance
     Commutativity-2-of-V2_+
     (z (V2_- x))))))

(defthm
 V1_-_cancellation-on-left
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_+ x (V1_+ (V1_- x) y)) y))
 :hints (("Goal"
     :in-theory (disable V1_-_cancellation-on-right)
     :use V1_-_cancellation-on-right)))

(defthm
 V2_-_cancellation-on-left
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_+ x (V2_+ (V2_- x) y)) y))
 :hints (("Goal"
     :in-theory (disable V2_-_cancellation-on-right
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF))
     :use V2_-_cancellation-on-right)))

(defthm
 V1_0-is-only-V1_+_idempotent
 (implies (V1p x)
     (equal (equal (V1_+ x x) x)
      (equal x (V1_0))))
 :hints (("Goal"
     :use (:instance
     (:theorem
      (implies (equal x y)
         (equal (V1_+ x z)(V1_+ y z))))
     (x (V1_+ x x))
     (y x)
     (z (V1_- x))))))

(defthm
 V2_0-is-only-V2_+_idempotent
 (implies (V2p x)
     (equal (equal (V2_+ x x) x)
      (equal x (V2_0))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF))
     :use (:instance
     (:theorem
      (implies (equal x y)
         (equal (V2_+ x z)(V2_+ y z))))
     (x (V2_+ x x))
     (y x)
     (z (V2_- x))))))

(defthm
 V2_0-def 
 (equal (V2_0)
   (cons (V1_0)(V1_0)))
 :rule-classes :definition
 :hints (("Goal"
     :in-theory (disable V2_0-is-only-V2_+_idempotent)
     :use (:instance
     V2_0-is-only-V2_+_idempotent
     (x (cons (V1_0)(V1_0)))))))

(defthm
 S1_*-0=V1_0
 (implies (V1p x)
     (equal (S1_* 0 x)(V1_0)))
 :hints (("Goal"
     :in-theory (disable Distributivity-S1_*-scalar-+)
    :use (:instance
    Distributivity-S1_*-scalar-+
    (a 0)
    (b 0)))))

(defthm
 S2_*-0=V2_0
 (implies (V2p x)
     (equal (S2_* 0 x)(V2_0)))
 :hints (("Goal"
     :in-theory (disable Distributivity-S2_*-scalar-+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF))
    :use (:instance
    Distributivity-S2_*-scalar-+
    (a 0)
    (b 0)))))

(defthm
 S1_*-V1_0=V1_0
 (implies (real/rationalp a)
     (equal (S1_* a (V1_0))(V1_0)))
 :hints (("Goal"
     :in-theory (disable Distributivity-S1_*-V1_+)
     :use (:instance
     Distributivity-S1_*-V1_+
     (x (V1_0))
     (y (V1_0))))))

(defthm
 S2_*-V2_0=V2_0
 (implies (real/rationalp a)
     (equal (S2_* a (V2_0))(V2_0)))
 :hints (("Goal"
     :in-theory (disable Distributivity-S2_*-V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     Distributivity-S2_*-V2_+
     (x (V2_0))
     (y (V2_0))))))

(defthm
 V1_-_is-unique
 (implies (and (V1p x)
    (V1p y))
     (equal (equal (V1_+ x y)(V1_0))
      (equal y (V1_- x))))
 :hints (("Goal"
     :use (:instance
     (:theorem
      (implies (equal x y)
         (equal (V1_+ x z)(V1_+ y z))))
     (x (V1_+ x y))
     (y (V1_0))
     (z (V1_- x))))))

(defthm
 V2_-_is-unique
 (implies (and (V2p x)
    (V2p y))
     (equal (equal (V2_+ x y)(V2_0))
      (equal y (V2_- x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     (:theorem
      (implies (equal x y)
         (equal (V2_+ x z)(V2_+ y z))))
     (x (V2_+ x y))
     (y (V2_0))
     (z (V2_- x))))))

(defthm
 V2_-_def-rewrite
 (implies (V2p x)
     (equal (V2_- x)
      (cons (V1_- (car x))
      (V1_- (cdr x)))))
 :hints (("Goal"
     :in-theory (disable V2_-_is-unique)
     :use (:instance
     V2_-_is-unique
     (y (cons (V1_- (car x))
        (V1_- (cdr x))))))))

#|=========================
(defthm
 Vector2-closure-V2_-
 (implies (V2p x)
     (V2p (V2_- x))))
=================|#

(defthm
 S1_*_-a=V1_-_S1_*
 (implies (and (real/rationalp a)
    (V1p x))
     (equal (S1_* (- a) x)(V1_- (S1_* a x))))
 :hints (("Goal"
     :in-theory (disable Distributivity-S1_*-scalar-+)
     :use (:instance
     Distributivity-S1_*-scalar-+
     (b (- a))))))

(defthm
 S2_*_-a=V2_-_S2_*
 (implies (and (real/rationalp a)
    (V2p x))
     (equal (S2_* (- a) x)(V2_- (S2_* a x))))
 :hints (("Goal"
     :in-theory (disable Distributivity-S2_*-scalar-+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2_-_DEF-REWRITE
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     Distributivity-S2_*-scalar-+
     (b (- a))))))

(defthm
 S1_*_V1_-=V1_-_S1_*
 (implies (and (real/rationalp a)
    (V1p x))
     (equal (S1_* a (V1_- x))(V1_- (S1_* a x))))
 :hints (("Goal"
     :in-theory (disable Distributivity-S1_*-V1_+)
     :use (:instance
     Distributivity-S1_*-V1_+
     (y (V1_- x))))))

(defthm
 S2_*_V2_-=V2_-_S2_*
 (implies (and (real/rationalp a)
    (V2p x))
     (equal (S2_* a (V2_- x))(V2_- (S2_* a x))))
 :hints (("Goal"
     :in-theory (disable Distributivity-S2_*-V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2_-_DEF-REWRITE
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     Distributivity-S2_*-V2_+
     (y (V2_- x))))))

(defthm
 Distributivity-V1_-_over-V1_+
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_- (V1_+ x y))(V1_+ (V1_- x)(V1_- y))))
 :hints (("Goal"
     :in-theory (disable V1_-_is-unique)
     :use (:instance
     V1_-_is-unique
     (x (V1_+ x y))
     (y (V1_+ (V1_- x)(V1_- y)))))))

(defthm
 Distributivity-V2_-_over-V2_+
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_- (V2_+ x y))(V2_+ (V2_- x)(V2_- y))))
 :hints (("Goal"
     :in-theory (disable V2_-_is-unique
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2_-_DEF-REWRITE
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     V2_-_is-unique
     (x (V2_+ x y))
     (y (V2_+ (V2_- x)(V2_- y)))))))

(defthm
 V1_-_V1_-_x=x
 (implies (V1p x)
     (equal (V1_- (V1_- x)) x))
 :hints (("Goal"
     :in-theory (disable V1_-_is-unique)
     :use (:instance
     V1_-_is-unique
     (x (V1_- x))
     (y x)))))

(defthm
 V2_-_V2_-_x=x
 (implies (V2p x)
     (equal (V2_- (V2_- x)) x))
 :hints (("Goal"
     :in-theory (disable V2_-_is-unique
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2_-_DEF-REWRITE
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     V2_-_is-unique
     (x (V2_- x))
     (y x)))))

;; Vector multiplication theorems:
(defthm
 V1_*-S1_*=S1_*-V1_*-left
 (implies (and (real/rationalp a)
    (V1p x)
    (V1p y))
     (equal (V1_* (S1_* a x) y)
      (S1_* a (V1_* x y))))
 :hints (("Goal"
     :in-theory (disable Right-Distributivity-V1_*_V1_+)
     :use (:instance
     Right-Distributivity-V1_*_V1_+
     (b 0)
     (z y)))))

(defthm
 V2_*-S2_*=S2_*-V2_*-left
 (implies (and (real/rationalp a)
    (V2p x)
    (V2p y))
     (equal (V2_* (S2_* a x) y)
      (S2_* a (V2_* x y))))
 :hints (("Goal"
     :in-theory (disable Right-Distributivity-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2_-_DEF-REWRITE
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     Right-Distributivity-V2_*_V2_+
     (b 0)
     (z y)))))

(defthm
 V1_*-S1_*=S1_*-V1_*-right
 (implies (and (real/rationalp a)
    (V1p x)
    (V1p y))
     (equal (V1_* x (S1_* a y))
      (S1_* a (V1_* x y))))
 :hints (("Goal"
     :in-theory (disable Left-Distributivity-V1_*_V1_+)
     :use (:instance
     Left-Distributivity-V1_*_V1_+
     (b 0)
     (z y)))))

(defthm
 V2_*-S2_*=S2_*-V2_*-right
 (implies (and (real/rationalp a)
    (V2p x)
    (V2p y))
     (equal (V2_* x (S2_* a y))
      (S2_* a (V2_* x y))))
 :hints (("Goal"
     :in-theory (disable Left-Distributivity-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2_-_DEF-REWRITE
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     Left-Distributivity-V2_*_V2_+
     (b 0)
     (z y)))))

(defthm
 V1_*-V1_0=V1_0-left
 (implies (V1p x)
     (equal (V1_* (V1_0) x)(V1_0)))
 :hints (("Goal"
     :in-theory (disable Right-Distributivity-V1_*_V1_+)
     :use (:instance
     Right-Distributivity-V1_*_V1_+
     (a 1)
     (b 1)
     (x (V1_0))
     (y (V1_0))
     (z x)))))

(defthm
 V2_*-V2_0=V2_0-left
 (implies (V2p x)
     (equal (V2_* (V2_0) x)(V2_0)))
 :hints (("Goal"
     :in-theory (disable Right-Distributivity-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2_-_DEF-REWRITE
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     Right-Distributivity-V2_*_V2_+
     (a 1)
     (b 1)
     (x (V2_0))
     (y (V2_0))
     (z x)))))

(defthm
 V1_*-V1_0=V1_0-right
 (implies (V1p x)
     (equal (V1_* x (V1_0))(V1_0)))
 :hints (("Goal"
     :in-theory (disable Left-Distributivity-V1_*_V1_+)
     :use (:instance
     Left-Distributivity-V1_*_V1_+
     (a 1)
     (b 1)
     (y (V1_0))
     (z (V1_0))))))

(defthm
 V2_*-V2_0=V2_0-right
 (implies (V2p x)
     (equal (V2_* x (V2_0))(V2_0)))
 :hints (("Goal"
     :in-theory (disable Left-Distributivity-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2_-_DEF-REWRITE
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     Left-Distributivity-V2_*_V2_+
     (a 1)
     (b 1)
     (y (V2_0))
     (z (V2_0))))))

(defthm
 V1_*-V1_-=V1_-V1_*-left
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_* (V1_- x) y)
      (V1_- (V1_* x y))))
 :hints (("Goal"
     :in-theory (disable Right-Distributivity-V1_*_V1_+)
     :use (:instance
     Right-Distributivity-V1_*_V1_+
     (a 1)
     (b 1)
     (y (V1_- x))
     (z y)))))

(defthm
 V2_*-V2_-=V2_-V2_*-left
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_* (V2_- x) y)
      (V2_- (V2_* x y))))
 :hints (("Goal"
     :in-theory (disable Right-Distributivity-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2_-_DEF-REWRITE
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     Right-Distributivity-V2_*_V2_+
     (a 1)
     (b 1)
     (y (V2_- x))
     (z y)))))

(defthm
 V1_*-V1_-=V1_-V1_*-right
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_* x (V1_- y))
      (V1_- (V1_* x y))))
 :hints (("Goal"
     :in-theory (disable Left-Distributivity-V1_*_V1_+)
     :use (:instance
     Left-Distributivity-V1_*_V1_+
     (a 1)
     (b 1)
     (y (V1_- y))
     (z y)))))

(defthm
 V2_*-V2_-=V2_-V2_*-right
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_* x (V2_- y))
      (V2_- (V2_* x y))))
 :hints (("Goal"
     :in-theory (disable Left-Distributivity-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2_-_DEF-REWRITE
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     Left-Distributivity-V2_*_V2_+
     (a 1)
     (b 1)
     (y (V2_- y))
     (z y)))))

;; Vector Norm and Dot Product theorems:
(defthm
 V1_norm-V1_1=1
 (equal (V1_norm (V1_1)) 1)
 :hints (("Goal"
     :in-theory (disable V1-Composition-Law)
     :use (:instance
     V1-Composition-Law
     (x (V1_1))
     (y (V1_1))))))

(defthm
 V2_norm-V2_1=1
 (equal (V2_norm (V2_1)) 1)
 :hints (("Goal"
     :in-theory (disable V2-Composition-Law
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2_-_DEF-REWRITE
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     V2-Composition-Law
     (x (V2_1))
     (y (V2_1))))))

(defthm
 V1_norm-V1_0=0
 (equal (V1_norm (V1_0)) 0))

(defthm
 V2_norm-V2_0=0
 (equal (V2_norm (V2_0)) 0)
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2_-_DEF-REWRITE
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF)))))

(defthmD
 Realp>=0-V1_norm-forward-chaining
 (implies (V1p x)
     (and (real/rationalp (V1_norm x))
    (>= (V1_norm x) 0)))
 :rule-classes :forward-chaining)

(defthmD
 Realp>=0-V2_norm-forward-chaining
 (implies (V2p x)
     (and (real/rationalp (V2_norm x))
    (>= (V2_norm x) 0)))
 :rule-classes :forward-chaining
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2_-_DEF-REWRITE
             (:DEFINITION V2_0-DEF)
             (:DEFINITION S2_*-DEF)))))

(defthm
 V1_0-is-only-zero-divisor
 (implies (and (V1p x)
    (V1p y))
     (equal (equal (V1_* x y)(V1_0))
      (or (equal x (V1_0))
          (equal y (V1_0)))))
 :hints (("Goal"
     :in-theory (e/d (Realp>=0-V1_norm-forward-chaining)
         (ZERO-IS-ONLY-ZERO-DIVISOR
          V1-Composition-Law))
     :use (V1-Composition-Law
     (:instance
      ZERO-IS-ONLY-ZERO-DIVISOR
      (x (V1_norm x))
      (y (V1_norm y)))))))

(defthm
 V2_0-is-only-zero-divisor
 (implies (and (V2p x)
    (V2p y))
     (equal (equal (V2_* x y)(V2_0))
      (or (equal x (V2_0))
          (equal y (V2_0)))))
 :hints (("Goal"
     :in-theory (e/d (Realp>=0-V2_norm-forward-chaining)
         (ZERO-IS-ONLY-ZERO-DIVISOR
          V2-Composition-Law
          (:DEFINITION V2P-DEF)
          (:DEFINITION V2_+-DEF)
          V2_-_DEF-REWRITE
          (:DEFINITION V2_0-DEF)
          (:DEFINITION S2_*-DEF)))
     :use (V2-Composition-Law
     (:instance
      ZERO-IS-ONLY-ZERO-DIVISOR
      (x (V2_norm x))
      (y (V2_norm y)))))))

(defthm
 Realp-V1_dot
 (implies (and (V1p x)
    (V1p y))
     (real/rationalp (V1_dot x y))))

(defthm
 Realp-V2_dot
 (implies (and (V2p x)
    (V2p y))
     (real/rationalp (V2_dot x y)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)))))

(defthmD
 Realp-V1_dot-forward-chaining
 (implies (and (V1p x)
    (V1p y))
     (real/rationalp (V1_dot x y)))
 :rule-classes :forward-chaining)

(defthmD
 Realp-V2_dot-forward-chaining
 (implies (and (V2p x)
    (V2p y))
     (real/rationalp (V2_dot x y)))
 :rule-classes :forward-chaining
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)))))

(defthm
 Commmutativity-of-V1dot
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_dot x y)
      (V1_dot y x))))

(defthm
 Commmutativity-of-V2dot
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_dot x y)
      (V2_dot y x)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)))))

(defthm
 V1_dot-V1_0
 (implies (V1p x)
     (equal (V1_dot x (V1_0)) 0)))

(defthm
 V2_dot-V2_0
 (implies (V2p x)
     (equal (V2_dot x (V2_0)) 0))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_0-DEF)
             (:DEFINITION V2_+-DEF)))))

(defthm
 V1-Scaling-law-left
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot (V1_* x y)
        (V1_* x z))
      (* (V1_norm x)
         (V1_dot y z))))
 :hints (("Subgoal 2"
     :in-theory (disable LEFT-DISTRIBUTIVITY-V1_*_V1_+)
     :use (:instance
     LEFT-DISTRIBUTIVITY-V1_*_V1_+
     (a 1)
     (b 1)))
    ("Subgoal 1"
     :use (:theorem
     (implies (and (V1p x)
             (V1p y)
             (V1p z))
        (real/rationalp (V1_norm (V1_+ (V1_* X Y) (V1_* X Z)))))))))

(defthm
 V2-Scaling-law-left
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot (V2_* x y)
        (V2_* x z))
      (* (V2_norm x)
         (V2_dot y z))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_0-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)))
    ("Subgoal 2"
     :in-theory (disable LEFT-DISTRIBUTIVITY-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_0-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     LEFT-DISTRIBUTIVITY-V2_*_V2_+
     (a 1)
     (b 1)))
    ("Subgoal 1"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_0-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:theorem
     (implies (and (V2p x)
             (V2p y)
             (V2p z))
        (real/rationalp (V2_norm (V2_+ (V2_* X Y) (V2_* X Z)))))))))

(defthm
 V1-Scaling-law-right
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot (V1_* x z)
        (V1_* y z))
      (* (V1_dot x y)
         (V1_norm z))))
 :hints (("Subgoal 2"
     :in-theory (disable right-DISTRIBUTIVITY-V1_*_V1_+)
     :use (:instance
     right-DISTRIBUTIVITY-V1_*_V1_+
     (a 1)
     (b 1)))
    ("Subgoal 1"
     :use (:theorem
     (implies (and (V1p x)
             (V1p y)
             (V1p z))
        (real/rationalp (V1_norm (V1_+ (V1_* X z) (V1_* y Z)))))))))

(defthm
 V2-Scaling-law-right
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot (V2_* x z)
        (V2_* y z))
      (* (V2_dot x y)
         (V2_norm z))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_0-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)))
    ("Subgoal 2"
     :in-theory (disable right-DISTRIBUTIVITY-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_0-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance
     right-DISTRIBUTIVITY-V2_*_V2_+
     (a 1)
     (b 1)))
    ("Subgoal 1"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_0-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:theorem
     (implies (and (V2p x)
             (V2p y)
             (V2p z))
        (real/rationalp (V2_norm (V2_+ (V2_* X z) (V2_* y Z)))))))))

(defthm
 Distributivity-V1_dot-V1_+-right
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot x 
        (V1_+ (S1_* a y)
        (S1_* b z)))
      (+ (* a (V1_dot x y))
         (* b (V1_dot x z)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             Distributivity-V1_dot-V1_+)
     :use (:instance 
     Distributivity-V1_dot-V1_+
     (x y)
     (y z)
     (z x)))))

(defthm
 Distributivity-V2_dot-V2_+-right
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot x 
        (V2_+ (S2_* a y)
        (S2_* b z)))
      (+ (* a (V2_dot x y))
         (* b (V2_dot x z)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             Distributivity-V2_dot-V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_0-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF))
     :use (:instance 
     Distributivity-V2_dot-V2_+
     (x y)
     (y z)
     (z x)))))

(defthm
 Distributivity-V1_dot-V1_+-left&right
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (real/rationalp c)
    (real/rationalp d)
               (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot (V1_+ (S1_* a u)
        (S1_* b x))
        (V1_+ (S1_* c y)
        (S1_* d z)))
      (+ (* a c (V1_dot u y))
         (* a d (V1_dot u z))
         (* b c (V1_dot x y))
         (* b d (V1_dot x z)))))         
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)))))

(defthm
 Distributivity-V2_dot-V2_+-left&right
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (real/rationalp c)
    (real/rationalp d)
               (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot (V2_+ (S2_* a u)
        (S2_* b x))
        (V2_+ (S2_* c y)
        (S2_* d z)))
      (+ (* a c (V2_dot u y))
         (* a d (V2_dot u z))
         (* b c (V2_dot x y))
         (* b d (V2_dot x z)))))         
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_0-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)))))

(defthm
 V1-Exchange-Law-Lemma-a
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot (V1_* (V1_+ u x) y)
        (V1_* (V1_+ u x) z))
      (V1_dot (V1_+ (V1_* u y)
        (V1_* x y))
        (V1_+ (V1_* u z)
        (V1_* x z)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             V1-Scaling-law-left
             Right-Distributivity-V1_*_V1_+)
    :use ((:instance
     Right-Distributivity-V1_*_V1_+
     (a 1)
     (b 1)
     (x u)
     (y x)
     (z y))
    (:instance
     Right-Distributivity-V1_*_V1_+
     (a 1)
     (b 1)
     (x u)
     (y x))))))

(defthm
 V2-Exchange-Law-Lemma-a
 (implies (and (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot (V2_* (V2_+ u x) y)
        (V2_* (V2_+ u x) z))
      (V2_dot (V2_+ (V2_* u y)
        (V2_* x y))
        (V2_+ (V2_* u z)
        (V2_* x z)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2-Scaling-law-left
             Right-Distributivity-V2_*_V2_+)
    :use ((:instance
     Right-Distributivity-V2_*_V2_+
     (a 1)
     (b 1)
     (x u)
     (y x)
     (z y))
    (:instance
     Right-Distributivity-V2_*_V2_+
     (a 1)
     (b 1)
     (x u)
     (y x))))))

(defthm
 V1-Exchange-Law-Lemma-b
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot (V1_+ (V1_* u y)
        (V1_* x y))
        (V1_+ (V1_* u z)
        (V1_* x z)))
      (+ (V1_dot (V1_* u y)
           (V1_* u z))
         (V1_dot (V1_* u y)
           (V1_* x z))
         (V1_dot (V1_* x y)
           (V1_* u z))
         (V1_dot (V1_* x y)
           (V1_* x z)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             V1-SCALING-LAW-LEFT
             Distributivity-V1_dot-V1_+-left&right)
     :use (:instance
     Distributivity-V1_dot-V1_+-left&right
     (a 1)
     (b 1)
     (c 1)
     (d 1)
     (u (V1_* u y))
     (x (V1_* x y))
     (y (V1_* u z))
     (z (V1_* x z))))))

(defthm
 V2-Exchange-Law-Lemma-b
 (implies (and (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot (V2_+ (V2_* u y)
        (V2_* x y))
        (V2_+ (V2_* u z)
        (V2_* x z)))
      (+ (V2_dot (V2_* u y)
           (V2_* u z))
         (V2_dot (V2_* u y)
           (V2_* x z))
         (V2_dot (V2_* x y)
           (V2_* u z))
         (V2_dot (V2_* x y)
           (V2_* x z)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2-SCALING-LAW-LEFT
             Distributivity-V2_dot-V2_+-left&right)
     :use (:instance
     Distributivity-V2_dot-V2_+-left&right
     (a 1)
     (b 1)
     (c 1)
     (d 1)
     (u (V2_* u y))
     (x (V2_* x y))
     (y (V2_* u z))
     (z (V2_* x z))))))

(defthm
 V1-Exchange-Law-Lemma-c
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot (V1_* (V1_+ u x) y)
        (V1_* (V1_+ u x) z))
      (+ (V1_dot (V1_* u y)
           (V1_* u z))
         (V1_dot (V1_* u y)
           (V1_* x z))
         (V1_dot (V1_* x y)
           (V1_* u z))
         (V1_dot (V1_* x y)
           (V1_* x z))))))

(defthm
 V2-Exchange-Law-Lemma-c
 (implies (and (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot (V2_* (V2_+ u x) y)
        (V2_* (V2_+ u x) z))
      (+ (V2_dot (V2_* u y)
           (V2_* u z))
         (V2_dot (V2_* u y)
           (V2_* x z))
         (V2_dot (V2_* x y)
           (V2_* u z))
         (V2_dot (V2_* x y)
           (V2_* x z)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)))))

(defthm
 V1-Exchange-Law-Lemma-d
 (implies (and (V1p u)
    (V1p x))
     (equal (+ (V1_norm u)
         (* 2 (V1_dot u x))
         (V1_norm x))
      (V1_norm (V1_+ u x))))
 :hints (("Goal"
     :in-theory (e/d (Realp>=0-V1_norm-forward-chaining)
         (REALP>=0-V1_NORM))
     :use (:instance
     REALP>=0-V1_NORM
     (x (V1_+ u x))))))

(defthm
 V2-Exchange-Law-Lemma-d
 (implies (and (V2p u)
    (V2p x))
     (equal (+ (V2_norm u)
         (* 2 (V2_dot u x))
         (V2_norm x))
      (V2_norm (V2_+ u x))))
 :hints (("Goal"
     :in-theory (e/d (Realp>=0-V2_norm-forward-chaining)
         (REALP>=0-V2_NORM
          (:DEFINITION V2P-DEF)
          (:DEFINITION V2_+-DEF)))
     :use (:instance
     REALP>=0-V2_NORM
     (x (V2_+ u x))))))

(defthm
 V1-Exchange-Law-Lemma-e
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (+ (V1_dot (V1_* u y)
           (V1_* u z))
         (V1_dot (V1_* u y)
           (V1_* x z))
         (V1_dot (V1_* x y)
           (V1_* u z))
         (V1_dot (V1_* x y)
           (V1_* x z)))
      (* (+ (V1_norm u)
      (* 2 (V1_dot u x))
      (V1_norm x))
         (V1_dot y z))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             V1-SCALING-LAW-LEFT
             V1-Exchange-Law-Lemma-d)
     :use ((:instance 
      V1-SCALING-LAW-LEFT
      (x (V1_+ u x)))
     V1-Exchange-Law-Lemma-d))))

(defthm
 V2-Exchange-Law-Lemma-e
 (implies (and (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (+ (V2_dot (V2_* u y)
           (V2_* u z))
         (V2_dot (V2_* u y)
           (V2_* x z))
         (V2_dot (V2_* x y)
           (V2_* u z))
         (V2_dot (V2_* x y)
           (V2_* x z)))
      (* (+ (V2_norm u)
      (* 2 (V2_dot u x))
      (V2_norm x))
         (V2_dot y z))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2-SCALING-LAW-LEFT
             V2-Exchange-Law-Lemma-d)
     :use ((:instance 
      V2-SCALING-LAW-LEFT
      (x (V2_+ u x)))
     V2-Exchange-Law-Lemma-d))))

(defthm
 V1-Exchange-Law
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (+ (V1_dot (V1_* u y)
           (V1_* x z))
         (V1_dot (V1_* u z)
           (V1_* x y)))
      (* 2
         (V1_dot u x)
         (V1_dot y z))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             V1-Exchange-Law-Lemma-e)
     :use V1-Exchange-Law-Lemma-e)))

(defthm
 V2-Exchange-Law
 (implies (and (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (+ (V2_dot (V2_* u y)
           (V2_* x z))
         (V2_dot (V2_* u z)
           (V2_* x y)))
      (* 2
         (V2_dot u x)
         (V2_dot y z))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             V2-Exchange-Law-Lemma-e)
     :use V2-Exchange-Law-Lemma-e)))

(defun
 V1_conjugate (x)
 (V1_+ (S1_* (* 2 (V1_dot x (V1_1)))
        (V1_1))
  (V1_- x)))

(defun
 V2_conjugate (x)
 (V2_+ (S2_* (* 2 (V2_dot x (V2_1)))
        (V2_1))
  (V2_- x)))

(defthm
 V1p-V1_conjugate
 (implies (V1p x)
     (V1p (V1_conjugate x))))

(defthm
 V2p-V2_conjugate
 (implies (V2p x)
     (V2p (V2_conjugate x)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1_conjugate-V1_0=V1_0
 (equal (V1_conjugate (V1_0))
   (V1_0)))

(defthm
 V2_conjugate-V2_0=V2_0
 (equal (V2_conjugate (V2_0))
   (V2_0))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1_dot-S1_*=*-V1_dot-left
 (implies (and (real/rationalp a)
    (V1p x)
    (V1p y))
     (equal (V1_dot (S1_* a x) y)
      (* a (V1_dot x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             DISTRIBUTIVITY-V1_DOT-V1_+)
     :use (:instance
     DISTRIBUTIVITY-V1_DOT-V1_+
     (b 0)
     (z y)))))

(defthm
 V2_dot-S2_*=*-V2_dot-left
 (implies (and (real/rationalp a)
    (V2p x)
    (V2p y))
     (equal (V2_dot (S2_* a x) y)
      (* a (V2_dot x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             DISTRIBUTIVITY-V2_DOT-V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF))
     :use (:instance
     DISTRIBUTIVITY-V2_DOT-V2_+
     (b 0)
     (z y)))))

(defthm
 V1_dot-S1_*=*-V1_dot-right
 (implies (and (real/rationalp a)
    (V1p x)
    (V1p y))
     (equal (V1_dot x (S1_* a y))
      (* a (V1_dot x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             V1_dot-S1_*=*-V1_dot-left)
     :use (:instance
     V1_dot-S1_*=*-V1_dot-left
     (x y)
     (y x)))))

(defthm
 V2_dot-S2_*=*-V2_dot-right
 (implies (and (real/rationalp a)
    (V2p x)
    (V2p y))
     (equal (V2_dot x (S2_* a y))
      (* a (V2_dot x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             V2_dot-S2_*=*-V2_dot-left
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF))
     :use (:instance
     V2_dot-S2_*=*-V2_dot-left
     (x y)
     (y x)))))

(defthm
 V1_dot-V1_-=-_V1_dot-right
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_dot x (V1_- y))
      (- (V1_dot x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             V1_dot-S1_*=*-V1_dot-right)
     :use (:instance
     V1_dot-S1_*=*-V1_dot-right
     (a -1)))))

(defthm
 V2_dot-V2_-=-_V2_dot-right
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_dot x (V2_- y))
      (- (V2_dot x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             V2_dot-S2_*=*-V2_dot-right
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     V2_dot-S2_*=*-V2_dot-right
     (a -1)))))

(defthm
 V1_dot-V1_-=-_V1_dot-left
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_dot (V1_- x) y)
      (- (V1_dot x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)))))

(defthm
 V2_dot-V2_-=-_V2_dot-left
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_dot (V2_- x) y)
      (- (V2_dot x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1-Sum-conjugation
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_conjugate (V1_+ x y))
      (V1_+ (V1_conjugate x)
      (V1_conjugate y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             Distributivity-V1_dot-V1_+-right)
    :use (:instance
    Distributivity-V1_dot-V1_+-right
    (x (V1_1))
    (a 1)
    (b 1)
    (y x)
    (z y)))))

(defthm
 V2-Sum-conjugation
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_conjugate (V2_+ x y))
      (V2_+ (V2_conjugate x)
      (V2_conjugate y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             Distributivity-V2_dot-V2_+-right
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     Distributivity-V2_dot-V2_+-right
     (x (V2_1))
     (a 1)
     (b 1)
     (y x)
     (z y)))))

(defthmD
 V1-Braid-Law-1-lemma-a
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot y (V1_* (V1_conjugate x) z))
      (V1_dot y (V1_+ (S1_* (* 2 (V1_dot x (V1_1)))
          z)
          (V1_- (V1_* x z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             Right-Distributivity-V1_*_V1_+)
     :use (:instance
     Right-Distributivity-V1_*_V1_+
     (a 1)
     (b (* 2 (V1_DOT (V1_1) x)))
     (x (V1_- x))
     (y (V1_1))))))

(defthmD
 V2-Braid-Law-1-lemma-a
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot y (V2_* (V2_conjugate x) z))
      (V2_dot y (V2_+ (S2_* (* 2 (V2_dot x (V2_1)))
          z)
          (V2_- (V2_* x z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             Right-Distributivity-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     Right-Distributivity-V2_*_V2_+
     (a 1)
     (b (* 2 (V2_DOT (V2_1) x)))
     (x (V2_- x))
     (y (V2_1))))))

(defthmD
 V1-Braid-Law-2-lemma-a
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot x (V1_* z (V1_conjugate y)))
      (V1_dot x (V1_+ (S1_* (* 2 (V1_dot y (V1_1)))
          z)
          (V1_- (V1_* z y))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             Left-Distributivity-V1_*_V1_+)
     :use (:instance
     Left-Distributivity-V1_*_V1_+
     (a 1)
     (b (* 2 (V1_dot y (V1_1))))
     (x z)
     (y (V1_- y))
     (z (V1_1))))))

(defthmD
 V2-Braid-Law-2-lemma-a
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot x (V2_* z (V2_conjugate y)))
      (V2_dot x (V2_+ (S2_* (* 2 (V2_dot y (V2_1)))
          z)
          (V2_- (V2_* z y))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             Left-Distributivity-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     Left-Distributivity-V2_*_V2_+
     (a 1)
     (b (* 2 (V2_dot y (V2_1))))
     (x z)
     (y (V2_- y))
     (z (V2_1))))))

(defthmD
 V1-Braid-Law-1-lemma-b
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot y (V1_* (V1_conjugate x) z))
      (+ (* 2 
      (V1_dot x (V1_1))
      (V1_dot y z))
         (- (V1_dot y (V1_* x z))))))
 :hints (("Goal"
     :in-theory (e/d (V1-Braid-Law-1-lemma-a)
         ((:DEFINITION V1_DOT-DEF)
          (:DEFINITION V1_CONJUGATE)
          Distributivity-V1_dot-V1_+-right))
     :use (:instance
     Distributivity-V1_dot-V1_+-right
     (a 1)
     (b 1)
     (x y)
     (y (V1_- (V1_* x z)))
     (z (S1_* (* 2 (V1_DOT (V1_1) x)) z))))))

(defthmD
 V2-Braid-Law-1-lemma-b
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot y (V2_* (V2_conjugate x) z))
      (+ (* 2 
      (V2_dot x (V2_1))
      (V2_dot y z))
         (- (V2_dot y (V2_* x z))))))
 :hints (("Goal"
     :in-theory (e/d (V2-Braid-Law-1-lemma-a)
         ((:DEFINITION V2_DOT-DEF)
          (:DEFINITION V2_CONJUGATE)
          Distributivity-V2_dot-V2_+-right
          (:DEFINITION V2P-DEF)
          (:DEFINITION V2_+-DEF)
          (:DEFINITION S2_*-DEF)
          (:DEFINITION V2_0-DEF)
          V2_-_DEF-REWRITE))
     :use (:instance
     Distributivity-V2_dot-V2_+-right
     (a 1)
     (b 1)
     (x y)
     (y (V2_- (V2_* x z)))
     (z (S2_* (* 2 (V2_DOT (V2_1) x)) z))))))

(defthmD
 V1-Braid-Law-2-lemma-b
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot x (V1_* z (V1_conjugate y)))
      (+ (* 2 
      (V1_dot y (V1_1))
      (V1_dot x z))
         (- (V1_dot x (V1_* z y))))))
 :hints (("Goal"
     :in-theory (e/d (V1-Braid-Law-2-lemma-a)
         ((:DEFINITION V1_DOT-DEF)
          (:DEFINITION V1_CONJUGATE)
          Distributivity-V1_dot-V1_+-right))
     :use (:instance
     Distributivity-V1_dot-V1_+-right
     (a 1)
     (b 1)
     (y (V1_- (V1_* z y)))
     (z (S1_* (* 2 (V1_DOT (V1_1) y)) z))))))

(defthmD
 V2-Braid-Law-2-lemma-b
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot x (V2_* z (V2_conjugate y)))
      (+ (* 2 
      (V2_dot y (V2_1))
      (V2_dot x z))
         (- (V2_dot x (V2_* z y))))))
 :hints (("Goal"
     :in-theory (e/d (V2-Braid-Law-2-lemma-a)
         ((:DEFINITION V2_DOT-DEF)
          (:DEFINITION V2_CONJUGATE)
          Distributivity-V2_dot-V2_+-right
          (:DEFINITION V2P-DEF)
          (:DEFINITION V2_+-DEF)
          (:DEFINITION S2_*-DEF)
          (:DEFINITION V2_0-DEF)
          V2_-_DEF-REWRITE))
     :use (:instance
     Distributivity-V2_dot-V2_+-right
     (a 1)
     (b 1)
     (y (V2_- (V2_* z y)))
     (z (S2_* (* 2 (V2_DOT (V2_1) y)) z))))))

(defthm
 V1-Braid-Law-1
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot y (V1_* (V1_conjugate x) z))
      (V1_dot z (V1_* x y))))
 :hints (("Goal"
     :in-theory (e/d (V1-Braid-Law-1-lemma-b)
         ((:DEFINITION V1_DOT-DEF)
          (:DEFINITION V1_CONJUGATE)
          V1-Exchange-Law))
     :use (:instance
     V1-Exchange-Law
     (u (V1_1))))))

(defthm
 V2-Braid-Law-1
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot y (V2_* (V2_conjugate x) z))
      (V2_dot z (V2_* x y))))
 :hints (("Goal"
     :in-theory (e/d (V2-Braid-Law-1-lemma-b)
         ((:DEFINITION V2_DOT-DEF)
          (:DEFINITION V2_CONJUGATE)
          V2-Exchange-Law
          (:DEFINITION V2P-DEF)
          (:DEFINITION V2_+-DEF)
          (:DEFINITION S2_*-DEF)
          (:DEFINITION V2_0-DEF)
          V2_-_DEF-REWRITE))
     :use (:instance
     V2-Exchange-Law
     (u (V2_1))))))

(defthm
 V1-Braid-Law-2
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot x (V1_* z (V1_conjugate y)))
      (V1_dot z (V1_* x y))))
 :hints (("Goal"
     :in-theory (e/d (V1-Braid-Law-2-lemma-b)
         ((:DEFINITION V1_DOT-DEF)
          (:DEFINITION V1_CONJUGATE)
          V1-Exchange-Law))
     :use (:instance
     V1-Exchange-Law
     (u z)
     (z (V1_1))))))

(defthm
 V2-Braid-Law-2
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot x (V2_* z (V2_conjugate y)))
      (V2_dot z (V2_* x y))))
 :hints (("Goal"
     :in-theory (e/d (V2-Braid-Law-2-lemma-b)
         ((:DEFINITION V2_DOT-DEF)
          (:DEFINITION V2_CONJUGATE)
          V2-Exchange-Law
          (:DEFINITION V2P-DEF)
          (:DEFINITION V2_+-DEF)
          (:DEFINITION S2_*-DEF)
          (:DEFINITION V2_0-DEF)
          V2_-_DEF-REWRITE))
     :use (:instance
     V2-Exchange-Law
     (u z)
     (z (V2_1))))))

(defthm
 V1-Braid-Law-3
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot (V1_conjugate x) (V1_* y (V1_conjugate z)))
      (V1_dot z (V1_* x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)))))

(defthm
 V2-Braid-Law-3
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot (V2_conjugate x) (V2_* y (V2_conjugate z)))
      (V2_dot z (V2_* x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1-Braid-Law-4
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot (V1_conjugate y) (V1_* (V1_conjugate z) x))
      (V1_dot z (V1_* x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)))))

(defthm
 V2-Braid-Law-4
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot (V2_conjugate y) (V2_* (V2_conjugate z) x))
      (V2_dot z (V2_* x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1-Braid-Law-5
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot (V1_conjugate z) (V1_* (V1_conjugate y)(V1_conjugate x)))
      (V1_dot z (V1_* x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)))))

(defthm
 V2-Braid-Law-5
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot (V2_conjugate z) (V2_* (V2_conjugate y)(V2_conjugate x)))
      (V2_dot z (V2_* x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1-BiConjugation-lemma
 (implies (and (V1p x)
    (V1p u))
     (equal (V1_dot u (V1_conjugate (V1_conjugate x)))
      (V1_dot u x)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)
             V1-Braid-Law-1)
     :use ((:instance
      V1-Braid-Law-1
      (y (V1_1))
      (z u))
     (:instance
      V1-Braid-Law-1
      (x (V1_conjugate x))
      (y u)
      (z (V1_1)))))))

(defthm
 V2-BiConjugation-lemma
 (implies (and (V2p x)
    (V2p u))
     (equal (V2_dot u (V2_conjugate (V2_conjugate x)))
      (V2_dot u x)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             V2-Braid-Law-1
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use ((:instance
      V2-Braid-Law-1
      (y (V2_1))
      (z u))
     (:instance
      V2-Braid-Law-1
      (x (V2_conjugate x))
      (y u)
      (z (V2_1)))))))

(defun-sk
 Forall-u-V1_dot-u-x=V1_dot-u-y (x y)
 (forall (u)
    (implies (V1p u)
       (equal (V1_dot u x)
        (V1_dot u y))))
 :rewrite :direct)

(defun-sk
 Forall-u-V2_dot-u-x=V2_dot-u-y (x y)
 (forall (u)
    (implies (V2p u)
       (equal (V2_dot u x)
        (V2_dot u y))))
 :rewrite :direct)

(defthm
 Forall-u-V1_dot-u-x=V1_dot-u-y->Forall-u-V1_dot-u-x=0-lemma
 (implies (and (V1p x)
    (V1p y)
    (Forall-u-V1_dot-u-x=V1_dot-u-y x y))
     (implies (V1p u)
        (equal (V1_dot u (V1_+ x
             (V1_- y)))
         0)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION FORALL-U-V1_DOT-U-X=V1_DOT-U-Y)
             Forall-u-V1_dot-u-x=V1_dot-u-y-necc
             Distributivity-V1_dot-V1_+-right)
     :use (Forall-u-V1_dot-u-x=V1_dot-u-y-necc
     (:instance
      Distributivity-V1_dot-V1_+-right
      (x u)
      (a 1)
      (b -1)
      (y x)
      (z y))))))

(defthm
 Forall-u-V2_dot-u-x=V2_dot-u-y->Forall-u-V2_dot-u-x=0-lemma
 (implies (and (V2p x)
    (V2p y)
    (Forall-u-V2_dot-u-x=V2_dot-u-y x y))
     (implies (V2p u)
        (equal (V2_dot u (V2_+ x
             (V2_- y)))
         0)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION FORALL-U-V2_DOT-U-X=V2_DOT-U-Y)
             Forall-u-V2_dot-u-x=V2_dot-u-y-necc
             Distributivity-V2_dot-V2_+-right
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (Forall-u-V2_dot-u-x=V2_dot-u-y-necc
     (:instance
      Distributivity-V2_dot-V2_+-right
      (x u)
      (a 1)
      (b -1)
      (y x)
      (z y))))))

(defthm
 Forall-u-V1_dot-u-x=V1_dot-u-y->Forall-u-V1_dot-u-x=0
 (implies (and (V1p x)
    (V1p y)
    (Forall-u-V1_dot-u-x=V1_dot-u-y x y))
     (Forall-u-V1_dot-u-x=0 (V1_+ x
          (V1_- y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION FORALL-U-V1_DOT-U-X=V1_DOT-U-Y)))))

(defthm
 Forall-u-V2_dot-u-x=V2_dot-u-y->Forall-u-V2_dot-u-x=0
 (implies (and (V2p x)
    (V2p y)
    (Forall-u-V2_dot-u-x=V2_dot-u-y x y))
     (Forall-u-V2_dot-u-x=0 (V2_+ x
          (V2_- y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION FORALL-U-V2_DOT-U-X=V2_DOT-U-Y)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 Forall-u-V1_dot-u-x=V1_dot-u-y->x=y
 (implies (and (V1p x)
    (V1p y)
    (Forall-u-V1_dot-u-x=V1_dot-u-y x y))
     (equal x y))
 :rule-classes nil
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION FORALL-U-V1_DOT-U-X=V1_DOT-U-Y)
             V1_-_IS-UNIQUE)
     :use ((:instance
      Forall-u-V1_dot-u-x=0->x=V1_0
      (x (V1_+ x (V1_- y))))
     (:instance
      V1_-_IS-UNIQUE
      (y x)
      (x (V1_- y)))))))

(defthm
 Forall-u-V2_dot-u-x=V2_dot-u-y->x=y
 (implies (and (V2p x)
    (V2p y)
    (Forall-u-V2_dot-u-x=V2_dot-u-y x y))
     (equal x y))
 :rule-classes nil
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION FORALL-U-V2_DOT-U-X=V2_DOT-U-Y)
             V2_-_IS-UNIQUE
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use ((:instance
      Forall-u-V2_dot-u-x=0->x=V2_0
      (x (V2_+ x (V2_- y))))
     (:instance
      V2_-_IS-UNIQUE
      (y x)
      (x (V2_- y)))))))

(defthm
 V1-BiConjugation
 (implies (V1p x)
     (equal (V1_conjugate (V1_conjugate x))
      x))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE))
     :use (:instance
     Forall-u-V1_dot-u-x=V1_dot-u-y->x=y
     (x (V1_conjugate (V1_conjugate x)))
     (y x)))))

(defthm
 V2-BiConjugation
 (implies (V2p x)
     (equal (V2_conjugate (V2_conjugate x))
      x))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     Forall-u-V2_dot-u-x=V2_dot-u-y->x=y
     (x (V2_conjugate (V2_conjugate x)))
     (y x)))))

(defthmD
 V1-Product-conjugation-lemma-a
 (implies (and (V1p u)
    (V1p x)
    (V1p y))
     (equal (V1_dot u
        (V1_* (V1_conjugate y)
        (V1_conjugate x)))
      (V1_dot (V1_conjugate x)
        (V1_* y u))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)
             V1-Braid-Law-2))))

(defthmD
 V2-Product-conjugation-lemma-a
 (implies (and (V2p u)
    (V2p x)
    (V2p y))
     (equal (V2_dot u
        (V2_* (V2_conjugate y)
        (V2_conjugate x)))
      (V2_dot (V2_conjugate x)
        (V2_* y u))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             V2-Braid-Law-2
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthmD
 V1-Product-conjugation-lemma-b
 (implies (and (V1p u)
    (V1p x)
    (V1p y))
     (equal (V1_dot (V1_conjugate x)
        (V1_* y u))
      (V1_dot y
        (V1_* (V1_conjugate x)
        (V1_conjugate u)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)))))

(defthmD
 V2-Product-conjugation-lemma-b
 (implies (and (V2p u)
    (V2p x)
    (V2p y))
     (equal (V2_dot (V2_conjugate x)
        (V2_* y u))
      (V2_dot y
        (V2_* (V2_conjugate x)
        (V2_conjugate u)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthmD
 V1-Product-conjugation-lemma-c
 (implies (and (V1p u)
    (V1p x)
    (V1p y))
     (equal (V1_dot y
        (V1_* (V1_conjugate x)
        (V1_conjugate u)))
      (V1_dot (V1_conjugate u)
        (V1_* x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)
             V1-Braid-Law-2))))

(defthmD
 V2-Product-conjugation-lemma-c
 (implies (and (V2p u)
    (V2p x)
    (V2p y))
     (equal (V2_dot y
        (V2_* (V2_conjugate x)
        (V2_conjugate u)))
      (V2_dot (V2_conjugate u)
        (V2_* x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             V2-Braid-Law-2
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthmD
 V1-Product-conjugation-lemma-d
 (implies (and (V1p u)
    (V1p x)
    (V1p y))
     (equal (V1_dot (V1_conjugate u)
        (V1_* x y))
      (V1_dot (V1_conjugate u)
        (V1_* (V1_* x y)(V1_1)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)))))

(defthmD
 V2-Product-conjugation-lemma-d
 (implies (and (V2p u)
    (V2p x)
    (V2p y))
     (equal (V2_dot (V2_conjugate u)
        (V2_* x y))
      (V2_dot (V2_conjugate u)
        (V2_* (V2_* x y)(V2_1)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthmD
 V1-Product-conjugation-lemma-e
 (implies (and (V1p u)
    (V1p x)
    (V1p y))
     (equal (V1_dot (V1_conjugate u)
        (V1_* (V1_* x y)(V1_1)))
      (V1_dot (V1_1)
        (V1_* (V1_conjugate u)
        (V1_conjugate (V1_* x y))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)))))

(defthmD
 V2-Product-conjugation-lemma-e
 (implies (and (V2p u)
    (V2p x)
    (V2p y))
     (equal (V2_dot (V2_conjugate u)
        (V2_* (V2_* x y)(V2_1)))
      (V2_dot (V2_1)
        (V2_* (V2_conjugate u)
        (V2_conjugate (V2_* x y))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthmD
 V1-Product-conjugation-lemma-f
 (implies (and (V1p u)
    (V1p x)
    (V1p y))
     (equal (V1_dot (V1_1)
        (V1_* (V1_conjugate u)
        (V1_conjugate (V1_* x y))))
      (V1_dot u
        (V1_conjugate (V1_* x y)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)
             V1-Braid-Law-2))))

(defthmD
 V2-Product-conjugation-lemma-f
 (implies (and (V2p u)
    (V2p x)
    (V2p y))
     (equal (V2_dot (V2_1)
        (V2_* (V2_conjugate u)
        (V2_conjugate (V2_* x y))))
      (V2_dot u
        (V2_conjugate (V2_* x y)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             V2-Braid-Law-2
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1-Product-conjugation-lemma
 (implies (and (V1p u)
    (V1p x)
    (V1p y))
     (equal (V1_dot u
       (V1_* (V1_conjugate y)
             (V1_conjugate x)))
      (V1_dot u
       (V1_conjugate (V1_* x y)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)
             V1-Braid-Law-1
             V1-Braid-Law-2)
     :use (V1-Product-conjugation-lemma-a
     V1-Product-conjugation-lemma-b
     V1-Product-conjugation-lemma-c
     V1-Product-conjugation-lemma-d
     V1-Product-conjugation-lemma-e
     V1-Product-conjugation-lemma-f))))

(defthm
 V2-Product-conjugation-lemma
 (implies (and (V2p u)
    (V2p x)
    (V2p y))
     (equal (V2_dot u
       (V2_* (V2_conjugate y)
             (V2_conjugate x)))
      (V2_dot u
       (V2_conjugate (V2_* x y)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             V2-Braid-Law-1
             V2-Braid-Law-2
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (V2-Product-conjugation-lemma-a
     V2-Product-conjugation-lemma-b
     V2-Product-conjugation-lemma-c
     V2-Product-conjugation-lemma-d
     V2-Product-conjugation-lemma-e
     V2-Product-conjugation-lemma-f))))

(defthm
 V1-Product-conjugation
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_conjugate (V1_* x y))
      (V1_* (V1_conjugate y)
      (V1_conjugate x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE))
     :use (:instance
     Forall-u-V1_dot-u-x=V1_dot-u-y->x=y
     (x (V1_conjugate (V1_* x y)))
     (y (V1_* (V1_conjugate y)
        (V1_conjugate x)))))))

(defthm
 V2-Product-conjugation
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_conjugate (V2_* x y))
      (V2_* (V2_conjugate y)
      (V2_conjugate x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     Forall-u-V2_dot-u-x=V2_dot-u-y->x=y
     (x (V2_conjugate (V2_* x y)))
     (y (V2_* (V2_conjugate y)
        (V2_conjugate x)))))))

(defthm
 V1-Inverse-law-left-lemma-a
 (implies (and (V1p u)
    (V1p x)
    (V1p y))
     (equal (V1_dot u (V1_* (V1_conjugate x)
          (V1_* x y)))
      (* (V1_norm x)(V1_dot u y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)))))

(defthm
 V2-Inverse-law-left-lemma-a
 (implies (and (V2p u)
    (V2p x)
    (V2p y))
     (equal (V2_dot u (V2_* (V2_conjugate x)
          (V2_* x y)))
      (* (V2_norm x)(V2_dot u y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1-Inverse-law-left-lemma-b
 (implies (and (V1p u)
    (V1p x)
    (V1p y))
     (equal (V1_dot u (V1_* (V1_conjugate x)
          (V1_* x y)))
      (V1_dot u (S1_* (V1_norm x) y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)))))

(defthm
 V2-Inverse-law-left-lemma-b
 (implies (and (V2p u)
    (V2p x)
    (V2p y))
     (equal (V2_dot u (V2_* (V2_conjugate x)
          (V2_* x y)))
      (V2_dot u (S2_* (V2_norm x) y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1-Inverse-law-left
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_* (V1_conjugate x)
      (V1_* x y))
      (S1_* (V1_norm x) y)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE))
     :use (:instance
     Forall-u-V1_dot-u-x=V1_dot-u-y->x=y
     (x (V1_* (V1_conjugate x)
        (V1_* x y)))
     (y (S1_* (V1_norm x) y)))))) 

(defthm
 V2-Inverse-law-left
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_* (V2_conjugate x)
      (V2_* x y))
      (S2_* (V2_norm x) y)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     Forall-u-V2_dot-u-x=V2_dot-u-y->x=y
     (x (V2_* (V2_conjugate x)
        (V2_* x y)))
     (y (S2_* (V2_norm x) y)))))) 

(defthm
 V1-Inverse-law-right-lemma-a
 (implies (and (V1p u)
    (V1p x)
    (V1p y))
     (equal (V1_dot u (V1_* (V1_* y x)
          (V1_conjugate x)))
      (* (V1_norm x)(V1_dot u y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)))))

(defthm
 V2-Inverse-law-right-lemma-a
 (implies (and (V2p u)
    (V2p x)
    (V2p y))
     (equal (V2_dot u (V2_* (V2_* y x)
          (V2_conjugate x)))
      (* (V2_norm x)(V2_dot u y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1-Inverse-law-right-lemma-b
 (implies (and (V1p u)
    (V1p x)
    (V1p y))
     (equal (V1_dot u (V1_* (V1_* y x)
          (V1_conjugate x)))
      (V1_dot u (S1_* (V1_norm x) y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)))))

(defthm
 V2-Inverse-law-right-lemma-b
 (implies (and (V2p u)
    (V2p x)
    (V2p y))
     (equal (V2_dot u (V2_* (V2_* y x)
          (V2_conjugate x)))
      (V2_dot u (S2_* (V2_norm x) y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
                              (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1-Inverse-law-right
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_* (V1_* y x)
      (V1_conjugate x))
      (S1_* (V1_norm x) y)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE))
     :use (:instance
     Forall-u-V1_dot-u-x=V1_dot-u-y->x=y
     (x (V1_* (V1_* y x)
        (V1_conjugate x)))
     (y (S1_* (V1_norm x) y)))))) 

(defthm
 V2-Inverse-law-right
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_* (V2_* y x)
      (V2_conjugate x))
      (S2_* (V2_norm x) y)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     Forall-u-V2_dot-u-x=V2_dot-u-y->x=y
     (x (V2_* (V2_* y x)
        (V2_conjugate x)))
     (y (S2_* (V2_norm x) y)))))) 

(defun
 V1_/ (x)
 (if (and (V1p x)
     (not (equal x (V1_0))))
     (S1_* (/ (V1_norm x))
      (V1_conjugate x))
     (V1_0)))

(defun
 V2_/ (x)
 (if (and (V2p x)
     (not (equal x (V2_0))))
     (S2_* (/ (V2_norm x))
      (V2_conjugate x))
     (V2_0)))

(defthm
 V1p-V1_/
 (V1p (V1_/ x))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V1_DOT-DEF)))))

(defthm
 V2p-V2_/
 (V2p (V2_/ x))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1_norm>0
 (implies (and (V1p x)
    (not (equal x (V1_0))))
     (> (V1_norm x) 0))
 :rule-classes (:linear :rewrite)
 :hints (("Goal"
     :in-theory (disable V1_norm=0)
     :use V1_norm=0)))

(defthm
 V2_norm>0
 (implies (and (V2p x)
    (not (equal x (V2_0))))
     (> (V2_norm x) 0))
 :rule-classes (:linear :rewrite)
 :hints (("Goal"
     :in-theory (disable V2_norm=0
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use V2_norm=0)))

(defthm
 V1-Inverse-law-left-1
 (implies (and (V1p x)
    (not (equal x (V1_0)))
    (V1p y))
     (equal (V1_* (V1_/ x)
      (V1_* x y))
      y))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)
             V1_norm>0)
     :use V1_norm>0)))

(defthm
 V2-Inverse-law-left-1
 (implies (and (V2p x)
    (not (equal x (V2_0)))
    (V2p y))
     (equal (V2_* (V2_/ x)
      (V2_* x y))
      y))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             V2_norm>0
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use V2_norm>0)))

(defthm
 V1-Inverse-law-right-1
 (implies (and (V1p x)
    (not (equal x (V1_0)))
    (V1p y))
     (equal (V1_* (V1_* y x)
      (V1_/ x))
      y))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)
             V1_norm>0)
     :use V1_norm>0)))

(defthm
 V2-Inverse-law-right-1
 (implies (and (V2p x)
    (not (equal x (V2_0)))
    (V2p y))
     (equal (V2_* (V2_* y x)
      (V2_/ x))
      y))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             V2_norm>0
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use V2_norm>0)))

(defthm
 V1-Inverse-law-left-2
 (implies (V1p x)
     (equal (V1_* (V1_conjugate x) x)
      (S1_* (V1_norm x) (V1_1))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)
             V1-Inverse-law-left)
     :use (:instance
     V1-Inverse-law-left
     (y (V1_1))))))

(defthm
 V2-Inverse-law-left-2
 (implies (V2p x)
     (equal (V2_* (V2_conjugate x) x)
      (S2_* (V2_norm x) (V2_1))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             V2-Inverse-law-left
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     V2-Inverse-law-left
     (y (V2_1))))))

(defthm
 V1-Inverse-law-right-2
 (implies (V1p x)
     (equal (V1_* x (V1_conjugate x))
      (S1_* (V1_norm x) (V1_1))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)
             V1-Inverse-law-right)
     :use (:instance
     V1-Inverse-law-right
     (y (V1_1))))))

(defthm
 V2-Inverse-law-right-2
 (implies (V2p x)
     (equal (V2_* x (V2_conjugate x))
      (S2_* (V2_norm x) (V2_1))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             V2-Inverse-law-right
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     V2-Inverse-law-right
     (y (V2_1))))))

(defthm
 V1-Inverse-law-left-3
 (implies (and (V1p x)
    (not (equal x (V1_0))))
     (equal (V1_* (V1_/ x) x)
      (V1_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_/)
             V1-Inverse-law-left-1)
     :use (:instance
     V1-Inverse-law-left-1
     (y (V1_1))))))

(defthm
 V2-Inverse-law-left-3
 (implies (and (V2p x)
    (not (equal x (V2_0))))
     (equal (V2_* (V2_/ x) x)
      (V2_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_/)
             V2-Inverse-law-left-1
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     V2-Inverse-law-left-1
     (y (V2_1))))))

(defthm
 V1-Inverse-law-right-3
 (implies (and (V1p x)
    (not (equal x (V1_0))))
     (equal (V1_* x (V1_/ x))
      (V1_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_/)
             V1-Inverse-law-right-1)
     :use (:instance
     V1-Inverse-law-right-1
     (y (V1_1))))))

(defthm
 V2-Inverse-law-right-3
 (implies (and (V2p x)
    (not (equal x (V2_0))))
     (equal (V2_* x (V2_/ x))
      (V2_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_/)
             V2-Inverse-law-right-1
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     V2-Inverse-law-right-1
     (y (V2_1))))))

(defthm
 V1_conjugate-V1_1-is-V1_*-idempotent
 (equal (V1_* (V1_conjugate (V1_1))
         (V1_conjugate (V1_1)))
   (V1_conjugate (V1_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             V1-Product-conjugation)
    :use (:instance
    V1-Product-conjugation
    (x (V1_1))
    (y (V1_1))))))

(defthm
 V2_conjugate-V2_1-is-V2_*-idempotent
 (equal (V2_* (V2_conjugate (V2_1))
         (V2_conjugate (V2_1)))
   (V2_conjugate (V2_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_CONJUGATE)
             V2-Product-conjugation
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
    :use (:instance
    V2-Product-conjugation
    (x (V2_1))
    (y (V2_1))))))

(defthm
 not-V1_Conjugate-V1_1=V1_0
 (not (equal (V1_conjugate (V1_1))(V1_0)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             V1-BiConjugation)
     :use (:instance
     V1-BiConjugation
     (x (V1_1))))))

(defthm
 not-V2_Conjugate-V2_1=V2_0
 (not (equal (V2_conjugate (V2_1))(V2_0)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_CONJUGATE)
             V2-BiConjugation
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     V2-BiConjugation
     (x (V2_1))))))

(defthm
 V1_0&V1_1-only-V1_*_idempotents
 (implies (V1p x)
     (equal (equal (V1_* x x) x)
      (or (equal x (V1_0))
          (equal x (V1_1)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_/)
             V1-Inverse-law-left-1)
     :use (:instance
     V1-Inverse-law-left-1
     (y x)))))

(defthm
 V2_0&V2_1-only-V2_*_idempotents
 (implies (V2p x)
     (equal (equal (V2_* x x) x)
      (or (equal x (V2_0))
          (equal x (V2_1)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_/)
             V2-Inverse-law-left-1
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     V2-Inverse-law-left-1
     (y x)))))

(defthm
 V1_conjugate-V1_1=V1_1
 (equal (V1_conjugate (V1_1))
   (V1_1))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             V1_0&V1_1-only-V1_*_idempotents)
    :use (:instance
    V1_0&V1_1-only-V1_*_idempotents
    (x (V1_conjugate (V1_1)))))))

(defthm
 V2_conjugate-V2_1=V2_1
 (equal (V2_conjugate (V2_1))
   (V2_1))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_CONJUGATE)
             V2_0&V2_1-only-V2_*_idempotents
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
    :use (:instance
    V2_0&V2_1-only-V2_*_idempotents
    (x (V2_conjugate (V2_1)))))))

(defthm
 S1_*=V1_0-equals-a=0-or-x=V1_0
 (implies (and (real/rationalp a)
    (V1p x))
     (equal (equal (S1_* a x)(V1_0))
      (or (equal a 0)
          (equal x (V1_0)))))
 :hints (("Goal"
     :in-theory (disable Associativity-of-S1_*)
     :use (:instance
     Associativity-of-S1_*
     (a (/ a))
     (b a)))))

(defthm
 S2_*=V2_0-equals-a=0-or-x=V2_0
 (implies (and (real/rationalp a)
    (V2p x))
     (equal (equal (S2_* a x)(V2_0))
      (or (equal a 0)
          (equal x (V2_0)))))
 :hints (("Goal"
     :in-theory (disable Associativity-of-S2_*
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     Associativity-of-S2_*
     (a (/ a))
     (b a)))))

(defthm
 S1_*=S1_*-equals-a=b-or-x=V1_0
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (V1p x))
     (equal (equal (S1_* a x)(S1_* b x))
      (or (equal a b)
          (equal x (V1_0)))))
 :hints (("Goal"
     :in-theory (disable S1_*=V1_0-equals-a=0-or-x=V1_0)
     :use (:instance
     S1_*=V1_0-equals-a=0-or-x=V1_0
     (a (- a b))))))

(defthm
 S2_*=S2_*-equals-a=b-or-x=V2_0
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (V2p x))
     (equal (equal (S2_* a x)(S2_* b x))
      (or (equal a b)
          (equal x (V2_0)))))
 :hints (("Goal"
     :in-theory (disable S2_*=V2_0-equals-a=0-or-x=V2_0
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     S2_*=V2_0-equals-a=0-or-x=V2_0
     (a (- a b))))))

(defthm
 V1_norm-V1_conjugate=V1_norm
 (implies (V1p x)
     (equal (V1_norm (V1_conjugate x))
      (V1_norm x)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             S1_*=S1_*-equals-a=b-or-x=V1_0
             V1-INVERSE-LAW-LEFT-2
             V1-INVERSE-LAW-RIGHT-2)
    :use ((:instance
     S1_*=S1_*-equals-a=b-or-x=V1_0
     (a (V1_norm x))
     (b (V1_norm (V1_conjugate x)))
     (x (V1_1)))
    (:instance
     V1-INVERSE-LAW-LEFT-2
     (x (V1_conjugate x)))
    V1-INVERSE-LAW-RIGHT-2))))

(defthm
 V2_norm-V2_conjugate=V2_norm
 (implies (V2p x)
     (equal (V2_norm (V2_conjugate x))
      (V2_norm x)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_CONJUGATE)
             S2_*=S2_*-equals-a=b-or-x=V2_0
             V2-INVERSE-LAW-LEFT-2
             V2-INVERSE-LAW-RIGHT-2
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
    :use ((:instance
     S2_*=S2_*-equals-a=b-or-x=V2_0
     (a (V2_norm x))
     (b (V2_norm (V2_conjugate x)))
     (x (V2_1)))
    (:instance
     V2-INVERSE-LAW-LEFT-2
     (x (V2_conjugate x)))
    V2-INVERSE-LAW-RIGHT-2))))

(defthm
 V1-Alternative-law-1-lemma-a
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_* (V1_conjugate x)
      (V1_* x y))
      (V1_* (V1_* (V1_conjugate x)
            x)
      y)))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V1_CONJUGATE)))))

(defthm
 V2-Alternative-law-1-lemma-a
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_* (V2_conjugate x)
      (V2_* x y))
      (V2_* (V2_* (V2_conjugate x)
            x)
      y)))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1-Alternative-law-1-lemma-b
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_* (V1_conjugate x)
      (V1_* x y))
      (V1_+ (V1_- (V1_* X (V1_* X Y)))
      (S1_* (* 2 (V1_DOT (V1_1) X))
            (V1_* X Y)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             Right-Distributivity-V1_*_V1_+)
     :use (:instance
      Right-Distributivity-V1_*_V1_+
      (a 1)
      (b (* 2 (V1_DOT (V1_1) X)))
      (x (V1_- X))
      (y (V1_1))
      (z (V1_* x y))))))

(defthm
 V2-Alternative-law-1-lemma-b
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_* (V2_conjugate x)
      (V2_* x y))
      (V2_+ (V2_- (V2_* X (V2_* X Y)))
      (S2_* (* 2 (V2_DOT (V2_1) X))
            (V2_* X Y)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             Right-Distributivity-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
      Right-Distributivity-V2_*_V2_+
      (a 1)
      (b (* 2 (V2_DOT (V2_1) X)))
      (x (V2_- X))
      (y (V2_1))
      (z (V2_* x y))))))

(defthm
 V1-Alternative-law-1-lemma-c
 (implies (V1p x)
     (equal (V1_* (V1_conjugate x) x)
      (V1_+ (V1_- (V1_* x x))
      (S1_* (* 2 (V1_DOT (V1_1) X)) x))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             Right-Distributivity-V1_*_V1_+)
     :use (:instance
      Right-Distributivity-V1_*_V1_+
      (a 1)
      (b (* 2 (V1_DOT (V1_1) X)))
      (x (V1_- X))
      (y (V1_1))
      (z x)))))

(defthm
 V2-Alternative-law-1-lemma-c
 (implies (V2p x)
     (equal (V2_* (V2_conjugate x) x)
      (V2_+ (V2_- (V2_* x x))
      (S2_* (* 2 (V2_DOT (V2_1) X)) x))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             Right-Distributivity-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
      Right-Distributivity-V2_*_V2_+
      (a 1)
      (b (* 2 (V2_DOT (V2_1) X)))
      (x (V2_- X))
      (y (V2_1))
      (z x)))))

(defthm
 V1-Alternative-law-1-lemma-d
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_* (V1_* (V1_conjugate x) x)
      y)
      (V1_+ (V1_- (V1_* (V1_* x x) y))
      (S1_* (* 2 (V1_DOT (V1_1) X)) 
            (V1_* x y)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)
             Right-Distributivity-V1_*_V1_+)
     :use (:instance
      Right-Distributivity-V1_*_V1_+
      (a 1)
      (b (* 2 (V1_DOT (V1_1) X)))
      (x (V1_- (V1_* x x)))
      (y x)
      (z y)))))

(defthm
 V2-Alternative-law-1-lemma-d
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_* (V2_* (V2_conjugate x) x)
      y)
      (V2_+ (V2_- (V2_* (V2_* x x) y))
      (S2_* (* 2 (V2_DOT (V2_1) X)) 
            (V2_* x y)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             Right-Distributivity-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
      Right-Distributivity-V2_*_V2_+
      (a 1)
      (b (* 2 (V2_DOT (V2_1) X)))
      (x (V2_- (V2_* x x)))
      (y x)
      (z y)))))

(defthm
 V1-Alternative-law-1-lemma-e
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_+ (V1_- (V1_* X (V1_* X Y)))
      (S1_* (* 2 (V1_DOT (V1_1) X))
            (V1_* X Y)))
      (V1_+ (V1_- (V1_* (V1_* x x) y))
      (S1_* (* 2 (V1_DOT (V1_1) X)) 
            (V1_* x y)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)
             V1-Alternative-law-1-lemma-a
             V1-Alternative-law-1-lemma-c
             V1-INVERSE-LAW-LEFT-2)
     :use V1-Alternative-law-1-lemma-a)))

(defthm
 V2-Alternative-law-1-lemma-e
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_+ (V2_- (V2_* X (V2_* X Y)))
      (S2_* (* 2 (V2_DOT (V2_1) X))
            (V2_* X Y)))
      (V2_+ (V2_- (V2_* (V2_* x x) y))
      (S2_* (* 2 (V2_DOT (V2_1) X)) 
            (V2_* x y)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             V2-Alternative-law-1-lemma-a
             V2-Alternative-law-1-lemma-c
             V2-INVERSE-LAW-LEFT-2
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use V2-Alternative-law-1-lemma-a)))

(defthm
 V1_+-algebra-1
 (implies (and (V1p x)
    (V1p y))
    (equal (V1_+ (V1_+ x y)(V1_- y))
     x)))

(defthm
 V2_+-algebra-1
 (implies (and (V2p x)
    (V2p y))
    (equal (V2_+ (V2_+ x y)(V2_- y))
     x))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1_+-algebra-2
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (equal (V1_+ x z)
       (V1_+ y z))
      (equal x y)))
 :hints (("Goal"
     :in-theory (disable V1_+-algebra-1
             COMMUTATIVITY-OF-V1_+
             ASSOCIATIVITY-OF-V1_+) 
     :use ((:instance
      V1_+-algebra-1
      (y z))
     (:instance
      V1_+-algebra-1
      (x y)
      (y z))))))

(defthm
 V2_+-algebra-2
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (equal (V2_+ x z)
       (V2_+ y z))
      (equal x y)))
 :hints (("Goal"
     :in-theory (disable V2_+-algebra-1
             COMMUTATIVITY-OF-V2_+
             ASSOCIATIVITY-OF-V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE) 
     :use ((:instance
      V2_+-algebra-1
      (y z))
     (:instance
      V2_+-algebra-1
      (x y)
      (y z))))))

(defthm
 V1-Alternative-law-1-lemma-f
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_- (V1_* x (V1_* x y)))
      (V1_- (V1_* (V1_* x x) y))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             V1-Alternative-law-1-lemma-e)
     :use V1-Alternative-law-1-lemma-e)))

(defthm
 V2-Alternative-law-1-lemma-f
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_- (V2_* x (V2_* x y)))
      (V2_- (V2_* (V2_* x x) y))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             V2-Alternative-law-1-lemma-e
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use V2-Alternative-law-1-lemma-e)))

(defthm
 V1_-algebra-1
 (implies (and (V1p x)
    (V1p y))
     (equal (equal (V1_- x)(V1_- y))
      (equal x y)))
 :hints (("Goal"
     :in-theory (disable V1_-_V1_-_X=X)
     :use (V1_-_V1_-_X=X
     (:instance
      V1_-_V1_-_X=X
      (x y))))))

(defthm
 V2_-algebra-1
 (implies (and (V2p x)
    (V2p y))
     (equal (equal (V2_- x)(V2_- y))
      (equal x y)))
 :hints (("Goal"
     :in-theory (disable V2_-_V2_-_X=X
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (V2_-_V2_-_X=X
     (:instance
      V2_-_V2_-_X=X
      (x y))))))

(defthm
 V1-Alternative-law-1
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_* x (V1_* x y))
      (V1_* (V1_* x x) y)))
 :hints (("Goal" 
     :in-theory (disable V1-Alternative-law-1-lemma-f)
     :use V1-Alternative-law-1-lemma-f)))

(defthm
 V2-Alternative-law-1
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_* x (V2_* x y))
      (V2_* (V2_* x x) y)))
 :hints (("Goal" 
     :in-theory (disable V2-Alternative-law-1-lemma-f
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use V2-Alternative-law-1-lemma-f)))

(defthm
 V1-Alternative-law-2-lemma-a
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_* (V1_* y x)
      (V1_conjugate x))
      (V1_* y (V1_* x 
        (V1_conjugate x)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V1_CONJUGATE)))))

(defthm
 V2-Alternative-law-2-lemma-a
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_* (V2_* y x)
      (V2_conjugate x))
      (V2_* y (V2_* x 
        (V2_conjugate x)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthm
 V1-Alternative-law-2-lemma-b
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_* (V1_* y x)
      (V1_conjugate x))
      (V1_+ (V1_- (V1_* (V1_* y x) x))
      (S1_* (* 2 (V1_DOT (V1_1) x))
            (V1_* y x)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             Left-Distributivity-V1_*_V1_+)
     :use (:instance
      Left-Distributivity-V1_*_V1_+
      (a 1)
      (b (* 2 (V1_DOT (V1_1) x)))
      (x (V1_* y x))
      (y (V1_- x))
      (z (V1_1))))))

(defthm
 V2-Alternative-law-2-lemma-b
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_* (V2_* y x)
      (V2_conjugate x))
      (V2_+ (V2_- (V2_* (V2_* y x) x))
      (S2_* (* 2 (V2_DOT (V2_1) x))
            (V2_* y x)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             Left-Distributivity-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
      Left-Distributivity-V2_*_V2_+
      (a 1)
      (b (* 2 (V2_DOT (V2_1) x)))
      (x (V2_* y x))
      (y (V2_- x))
      (z (V2_1))))))

(defthm
 V1-Alternative-law-2-lemma-c
 (implies (V1p x)
     (equal (V1_* x (V1_conjugate x))
      (V1_+ (V1_- (V1_* x x))
      (S1_* (* 2 (V1_DOT (V1_1) x)) x))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             Left-Distributivity-V1_*_V1_+)
     :use (:instance
      Left-Distributivity-V1_*_V1_+
      (a 1)
      (b (* 2 (V1_DOT (V1_1) x)))
      (y (V1_- x))
      (z (V1_1))))))

(defthm
 V2-Alternative-law-2-lemma-c
 (implies (V2p x)
     (equal (V2_* x (V2_conjugate x))
      (V2_+ (V2_- (V2_* x x))
      (S2_* (* 2 (V2_DOT (V2_1) x)) x))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             Left-Distributivity-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
      Left-Distributivity-V2_*_V2_+
      (a 1)
      (b (* 2 (V2_DOT (V2_1) x)))
      (y (V2_- x))
      (z (V2_1))))))

(defthm
 V1-Alternative-law-2-lemma-d
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_* y
      (V1_* x (V1_conjugate x)))
      (V1_+ (V1_- (V1_* y (V1_* x x)))
      (S1_* (* 2 (V1_DOT (V1_1) x)) 
            (V1_* y x)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)
             Left-Distributivity-V1_*_V1_+)
     :use (:instance
      Left-Distributivity-V1_*_V1_+
      (a 1)
      (b (* 2 (V1_DOT (V1_1) x)))
      (x y)
      (y (V1_- (V1_* x x)))
      (z x)))))

(defthm
 V2-Alternative-law-2-lemma-d
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_* y
      (V2_* x (V2_conjugate x)))
      (V2_+ (V2_- (V2_* y (V2_* x x)))
      (S2_* (* 2 (V2_DOT (V2_1) x)) 
            (V2_* y x)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             Left-Distributivity-V2_*_V2_+
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
      Left-Distributivity-V2_*_V2_+
      (a 1)
      (b (* 2 (V2_DOT (V2_1) x)))
      (x y)
      (y (V2_- (V2_* x x)))
      (z x)))))

(defthm
 V1-Alternative-law-2-lemma-e
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_+ (V1_- (V1_* (V1_* y x) x))
      (S1_* (* 2 (V1_DOT (V1_1) x))
            (V1_* y x)))
      (V1_+ (V1_- (V1_* y (V1_* x x)))
      (S1_* (* 2 (V1_DOT (V1_1) x)) 
            (V1_* y x)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_CONJUGATE)
             V1-Alternative-law-2-lemma-a
             V1-Alternative-law-2-lemma-c
             V1_+-ALGEBRA-2
             V1_-ALGEBRA-1
             V1-INVERSE-LAW-right-2)
     :use V1-Alternative-law-2-lemma-a)))

(defthm
 V2-Alternative-law-2-lemma-e
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_+ (V2_- (V2_* (V2_* y x) x))
      (S2_* (* 2 (V2_DOT (V2_1) x))
            (V2_* y x)))
      (V2_+ (V2_- (V2_* y (V2_* x x)))
      (S2_* (* 2 (V2_DOT (V2_1) x)) 
            (V2_* y x)))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             V2-Alternative-law-2-lemma-a
             V2-Alternative-law-2-lemma-c
             V2_+-ALGEBRA-2
             V2_-ALGEBRA-1
             V2-INVERSE-LAW-right-2
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use V2-Alternative-law-2-lemma-a)))

(defthm
 V1-Alternative-law-2
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_* (V1_* y x) x)
      (V1_* y (V1_* x x))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             V1-Alternative-law-2-lemma-e)
     :use V1-Alternative-law-2-lemma-e)))

(defthm
 V2-Alternative-law-2
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_* (V2_* y x) x)
      (V2_* y (V2_* x x))))
 :hints (("Goal" 
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             V2-Alternative-law-2-lemma-e
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use V2-Alternative-law-2-lemma-e)))

(defthmD
 V1-Moufang-law-lemma-a
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot u (V1_* (V1_* x y)
          (V1_* z x)))
      (V1_dot (V1_* x y)
        (V1_* u
        (V1_* (V1_conjugate x)
              (V1_Conjugate z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_conjugate)
             V1-Braid-Law-2)
    :use (:instance
    V1-Braid-Law-2
    (x (V1_* x y))
    (y (V1_* z x))
    (z u)))))

(defthmD
 V2-Moufang-law-lemma-a
 (implies (and (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot u (V2_* (V2_* x y)
          (V2_* z x)))
      (V2_dot (V2_* x y)
        (V2_* u
        (V2_* (V2_conjugate x)
              (V2_Conjugate z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_conjugate)
             V2-Braid-Law-2
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
    :use (:instance
    V2-Braid-Law-2
    (x (V2_* x y))
    (y (V2_* z x))
    (z u)))))

(in-theory (disable V1-PRODUCT-CONJUGATION-LEMMA
        V2-PRODUCT-CONJUGATION-LEMMA))

(defthmD
 V1-Moufang-law-lemma-b
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot (V1_* x y)
        (V1_* u
        (V1_* (V1_conjugate x)
              (V1_Conjugate z))))
      (- (* 2 
      (V1_dot u x)
      (V1_dot y (V1_* (V1_conjugate x)
          (V1_Conjugate z))))
         (V1_dot (V1_* u y)
           (V1_* x
           (V1_* (V1_conjugate x)
           (V1_Conjugate z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_conjugate)
             V1-Braid-Law-1
             V1-Braid-Law-2
             V1-Exchange-Law)
     :use (:instance
     V1-Exchange-Law
     (y (V1_* (V1_conjugate x)
        (V1_Conjugate z)))
     (z y)))))

(defthmD
 V2-Moufang-law-lemma-b
 (implies (and (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot (V2_* x y)
        (V2_* u
        (V2_* (V2_conjugate x)
              (V2_Conjugate z))))
      (- (* 2 
      (V2_dot u x)
      (V2_dot y (V2_* (V2_conjugate x)
          (V2_Conjugate z))))
         (V2_dot (V2_* u y)
           (V2_* x
           (V2_* (V2_conjugate x)
           (V2_Conjugate z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_conjugate)
             V2-Braid-Law-1
             V2-Braid-Law-2
             V2-Exchange-Law
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     V2-Exchange-Law
     (y (V2_* (V2_conjugate x)
        (V2_Conjugate z)))
     (z y)))))

(defthmD
 V1-Moufang-law-lemma-c
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (- (* 2 
      (V1_dot u x)
      (V1_dot y (V1_* (V1_conjugate x)
          (V1_Conjugate z))))
         (V1_dot (V1_* u y)
           (V1_* x
           (V1_* (V1_conjugate x)
           (V1_Conjugate z)))))
      (- (* 2 
      (V1_dot u x)
      (V1_dot (V1_* y z)
        (V1_conjugate x)))
         (V1_dot (V1_* (V1_conjugate x)
           (V1_* u y))
           (V1_* (V1_conjugate x)
           (V1_Conjugate z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_conjugate)
             V1-Braid-Law-2
             V1-Braid-Law-1)
     :use ((:instance
      V1-Braid-Law-2
      (x y)
      (y z)
      (z (V1_conjugate x)))
     (:instance
      V1-Braid-Law-1
      (y (V1_* (V1_conjugate x)(V1_conjugate z)))
      (z (V1_* u y)))))))

(defthmD
 V2-Moufang-law-lemma-c
 (implies (and (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (- (* 2 
      (V2_dot u x)
      (V2_dot y (V2_* (V2_conjugate x)
          (V2_Conjugate z))))
         (V2_dot (V2_* u y)
           (V2_* x
           (V2_* (V2_conjugate x)
           (V2_Conjugate z)))))
      (- (* 2 
      (V2_dot u x)
      (V2_dot (V2_* y z)
        (V2_conjugate x)))
         (V2_dot (V2_* (V2_conjugate x)
           (V2_* u y))
           (V2_* (V2_conjugate x)
           (V2_Conjugate z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_conjugate)
             V2-Braid-Law-2
             V2-Braid-Law-1
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use ((:instance
      V2-Braid-Law-2
      (x y)
      (y z)
      (z (V2_conjugate x)))
     (:instance
      V2-Braid-Law-1
      (y (V2_* (V2_conjugate x)(V2_conjugate z)))
      (z (V2_* u y)))))))

(defthmD
 V1-Moufang-law-lemma-d
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (- (* 2 
      (V1_dot u x)
      (V1_dot (V1_* y z)
        (V1_conjugate x)))
         (V1_dot (V1_* (V1_conjugate x)
           (V1_* u y))
           (V1_* (V1_conjugate x)
           (V1_Conjugate z))))
      (- (* 2 
      (V1_dot u x)
      (V1_dot (V1_* y z)
        (V1_conjugate x)))
         (* (V1_norm x)
      (V1_dot (V1_* u y)
        (V1_Conjugate z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_conjugate)
             V1-Braid-Law-1
             V1-Braid-Law-2))))

(defthmD
 V2-Moufang-law-lemma-d
 (implies (and (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (- (* 2 
      (V2_dot u x)
      (V2_dot (V2_* y z)
        (V2_conjugate x)))
         (V2_dot (V2_* (V2_conjugate x)
           (V2_* u y))
           (V2_* (V2_conjugate x)
           (V2_Conjugate z))))
      (- (* 2 
      (V2_dot u x)
      (V2_dot (V2_* y z)
        (V2_conjugate x)))
         (* (V2_norm x)
      (V2_dot (V2_* u y)
        (V2_Conjugate z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_conjugate)
             V2-Braid-Law-1
             V2-Braid-Law-2
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthmD
 V1-Moufang-law-lemma-e
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (- (* 2 
      (V1_dot u x)
      (V1_dot (V1_* y z)
        (V1_conjugate x)))
         (* (V1_norm (V1_conjugate x))
      (V1_dot (V1_* u y)
        (V1_Conjugate z))))
      (- (* 2 
      (V1_dot u x)
      (V1_dot (V1_* y z)
        (V1_conjugate x)))
         (* (V1_norm x)
      (V1_dot u
        (V1_* (V1_conjugate z)
              (V1_conjugate y)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_conjugate)
             V1-Braid-Law-1
             V1-Braid-Law-2)
     :use (:instance
     V1-Braid-Law-2
     (x u)
     (z (V1_conjugate z))))))

(defthmD
 V2-Moufang-law-lemma-e
 (implies (and (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (- (* 2 
      (V2_dot u x)
      (V2_dot (V2_* y z)
        (V2_conjugate x)))
         (* (V2_norm (V2_conjugate x))
      (V2_dot (V2_* u y)
        (V2_Conjugate z))))
      (- (* 2 
      (V2_dot u x)
      (V2_dot (V2_* y z)
        (V2_conjugate x)))
         (* (V2_norm x)
      (V2_dot u
        (V2_* (V2_conjugate z)
              (V2_conjugate y)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_conjugate)
             V2-Braid-Law-1
             V2-Braid-Law-2
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     V2-Braid-Law-2
     (x u)
     (z (V2_conjugate z))))))

(defthm
 V1_dot-x-V1_conj-y=V1_dot-y-V1_conj-x
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_dot x (V1_conjugate y))
      (V1_dot y (V1_conjugate x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_conjugate)
             V1-Braid-Law-1
             V1-Braid-Law-2)
    :use ((:instance 
     V1-Braid-Law-1
     (z (V1_1)))
    (:instance
     V1-Braid-Law-2
     (z (V1_1)))))))

(defthm
 V2_dot-x-V2_conj-y=V2_dot-y-V2_conj-x
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_dot x (V2_conjugate y))
      (V2_dot y (V2_conjugate x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_conjugate)
             V2-Braid-Law-1
             V2-Braid-Law-2
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
    :use ((:instance 
     V2-Braid-Law-1
     (z (V2_1)))
    (:instance
     V2-Braid-Law-2
     (z (V2_1)))))))

(defthmD
 V1-Moufang-law-lemma-f
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (- (* 2 
      (V1_dot u x)
      (V1_dot (V1_* y z)
        (V1_conjugate x)))
         (* (V1_norm x)
      (V1_dot u
             (V1_* (V1_conjugate z)
             (V1_conjugate y)))))
      (- (* 2 
      (V1_dot u x)
      (V1_dot x
        (V1_conjugate (V1_* y z))))
         (* (V1_norm x)
      (V1_dot u
        (V1_conjugate (V1_* y z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_conjugate)))))

(defthmD
 V2-Moufang-law-lemma-f
 (implies (and (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (- (* 2 
      (V2_dot u x)
      (V2_dot (V2_* y z)
        (V2_conjugate x)))
         (* (V2_norm x)
      (V2_dot u
             (V2_* (V2_conjugate z)
             (V2_conjugate y)))))
      (- (* 2 
      (V2_dot u x)
      (V2_dot x
        (V2_conjugate (V2_* y z))))
         (* (V2_norm x)
      (V2_dot u
        (V2_conjugate (V2_* y z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_conjugate)
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE))))

(defthmD
 V1-Moufang-law-lemma-g
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot u (V1_* (V1_* x y)
          (V1_* z x)))
      (- (* 2 
      (V1_dot u x)
      (V1_dot x
        (V1_conjugate (V1_* y z))))
         (* (V1_norm x)
      (V1_dot u
        (V1_conjugate (V1_* y z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_conjugate)
             V1-PRODUCT-CONJUGATION
             V1-Braid-Law-2
             V1_DOT-X-V1_CONJ-Y=V1_DOT-Y-V1_CONJ-X)
     :use (V1-Moufang-law-lemma-a
     V1-Moufang-law-lemma-b
     V1-Moufang-law-lemma-c
     V1-Moufang-law-lemma-d
     V1-Moufang-law-lemma-e
     V1-Moufang-law-lemma-f))))

(defthmD
 V2-Moufang-law-lemma-g
 (implies (and (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot u (V2_* (V2_* x y)
          (V2_* z x)))
      (- (* 2 
      (V2_dot u x)
      (V2_dot x
        (V2_conjugate (V2_* y z))))
         (* (V2_norm x)
      (V2_dot u
        (V2_conjugate (V2_* y z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_conjugate)
             V2-PRODUCT-CONJUGATION
             V2-Braid-Law-2
             V2_DOT-X-V2_CONJ-Y=V2_DOT-Y-V2_CONJ-X
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (V2-Moufang-law-lemma-a
     V2-Moufang-law-lemma-b
     V2-Moufang-law-lemma-c
     V2-Moufang-law-lemma-d
     V2-Moufang-law-lemma-e
     V2-Moufang-law-lemma-f))))

(defthmD
 V1-Moufang-law-lemma-h
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (- (* 2 
      (V1_dot u x)
      (V1_dot x
        (V1_conjugate (V1_* y z))))
         (* (V1_norm x)
      (V1_dot u
        (V1_conjugate (V1_* y z)))))
      (V1_dot u 
        (V1_+ (S1_* (* 2
           (V1_dot x
             (V1_conjugate (V1_* y z))))
              x)
        (S1_* (- (V1_norm x))
              (V1_conjugate (V1_* y z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_conjugate)
             V1-PRODUCT-CONJUGATION
             Distributivity-V1_dot-V1_+-right)
     :use (:instance
     Distributivity-V1_dot-V1_+-right
     (x u)
     (a (* 2
           (V1_dot x
             (V1_conjugate (V1_* y z)))))
     (y x)
     (b (- (V1_norm x)))
     (z (V1_conjugate (V1_* y z)))))))

(defthmD
 V2-Moufang-law-lemma-h
 (implies (and (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (- (* 2 
      (V2_dot u x)
      (V2_dot x
        (V2_conjugate (V2_* y z))))
         (* (V2_norm x)
      (V2_dot u
        (V2_conjugate (V2_* y z)))))
      (V2_dot u 
        (V2_+ (S2_* (* 2
           (V2_dot x
             (V2_conjugate (V2_* y z))))
              x)
        (S2_* (- (V2_norm x))
              (V2_conjugate (V2_* y z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_conjugate)
             V2-PRODUCT-CONJUGATION
             Distributivity-V2_dot-V2_+-right
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     Distributivity-V2_dot-V2_+-right
     (x u)
     (a (* 2
           (V2_dot x
             (V2_conjugate (V2_* y z)))))
     (y x)
     (b (- (V2_norm x)))
     (z (V2_conjugate (V2_* y z)))))))

(defthm
 V1-Moufang-law-lemma-i
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot u (V1_* (V1_* x y)
          (V1_* z x))) 
      (V1_dot u 
        (V1_+ (S1_* (* 2
           (V1_dot x
             (V1_conjugate (V1_* y z))))
              x)
        (S1_* (- (V1_norm x))
              (V1_conjugate (V1_* y z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_conjugate)
             V1-PRODUCT-CONJUGATION)
     :use (V1-Moufang-law-lemma-g
     V1-Moufang-law-lemma-h))))

(defthm
 V2-Moufang-law-lemma-i
 (implies (and (V2p u)
    (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_dot u (V2_* (V2_* x y)
          (V2_* z x))) 
      (V2_dot u 
        (V2_+ (S2_* (* 2
           (V2_dot x
             (V2_conjugate (V2_* y z))))
              x)
        (S2_* (- (V2_norm x))
              (V2_conjugate (V2_* y z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_conjugate)
             V2-PRODUCT-CONJUGATION
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (V2-Moufang-law-lemma-g
     V2-Moufang-law-lemma-h))))

(defthmD
 V1-Moufang-law-lemma-j
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_* (V1_* x y)
      (V1_* z x)) 
      (V1_+ (S1_* (* 2
         (V1_dot x
           (V1_conjugate (V1_* y z))))
            x)
           (S1_* (- (V1_norm x))
          (V1_conjugate (V1_* y z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_conjugate)
             V1-PRODUCT-CONJUGATION)
     :use (:instance
     Forall-u-V1_dot-u-x=V1_dot-u-y->x=y
     (x (V1_* (V1_* x y)
        (V1_* z x)))
     (y (V1_+ (S1_* (* 2
           (V1_dot x
             (V1_conjugate (V1_* y z))))
        x)
        (S1_* (- (V1_norm x))
        (V1_conjugate (V1_* y z)))))))))

(defthmD
 V2-Moufang-law-lemma-j
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_* (V2_* x y)
      (V2_* z x)) 
      (V2_+ (S2_* (* 2
         (V2_dot x
           (V2_conjugate (V2_* y z))))
            x)
           (S2_* (- (V2_norm x))
           (V2_conjugate (V2_* y z))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_conjugate)
             V2-PRODUCT-CONJUGATION
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     Forall-u-V2_dot-u-x=V2_dot-u-y->x=y
     (x (V2_* (V2_* x y)
        (V2_* z x)))
     (y (V2_+ (S2_* (* 2
           (V2_dot x
             (V2_conjugate (V2_* y z))))
        x)
        (S2_* (- (V2_norm x))
        (V2_conjugate (V2_* y z)))))))))

(in-theory (disable V1-Moufang-law-lemma-i
        V2-Moufang-law-lemma-i))

(defthm
 V1-Moufang-law-1
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_* (V1_* x y)
      (V1_* z x))
      (V1_* x 
      (V1_* (V1_* y z)
            x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_conjugate)
             V1-PRODUCT-CONJUGATION)
     :use (V1-Moufang-law-lemma-j
     (:instance
      V1-Moufang-law-lemma-j
      (y (V1_1))
      (z (V1_* y z)))))))

(defthm
 V2-Moufang-law-1
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_* (V2_* x y)
      (V2_* z x))
      (V2_* x 
      (V2_* (V2_* y z)
            x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_conjugate)
             V2-PRODUCT-CONJUGATION
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (V2-Moufang-law-lemma-j
     (:instance
      V2-Moufang-law-lemma-j
      (y (V2_1))
      (z (V2_* y z)))))))

(defthm
 V1-Moufang-law-2
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_* (V1_* x 
            (V1_* y z))
      x)
      (V1_* x 
           (V1_* (V1_* y z)
           x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V1_conjugate)
             V1-PRODUCT-CONJUGATION)
     :use (V1-Moufang-law-lemma-j
     (:instance
      V1-Moufang-law-lemma-j
      (z (V1_1))
      (y (V1_* y z)))))))

(defthm
 V2-Moufang-law-2
 (implies (and (V2p x)
    (V2p y)
    (V2p z))
     (equal (V2_* (V2_* x 
            (V2_* y z))
      x)
      (V2_* x 
      (V2_* (V2_* y z)
            x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_conjugate)
             V2-PRODUCT-CONJUGATION
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (V2-Moufang-law-lemma-j
     (:instance
      V2-Moufang-law-lemma-j
      (z (V2_1))
      (y (V2_* y z)))))))

(defthm
 V1-Alternative-law-3
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_* (V1_* x y) x)
      (V1_* x (V1_* y x))))
 :hints (("Goal" 
     :in-theory (disable V1-Moufang-law-2)
     :use (:instance
     V1-Moufang-law-2
     (z (V1_1))))))

(defthm
 V2-Alternative-law-3
 (implies (and (V2p x)
    (V2p y))
     (equal (V2_* (V2_* x y) x)
      (V2_* x (V2_* y x))))
 :hints (("Goal" 
     :in-theory (disable V2-Moufang-law-2
             (:DEFINITION V2P-DEF)
             (:DEFINITION V2_+-DEF)
             (:DEFINITION S2_*-DEF)
             (:DEFINITION V2_0-DEF)
             V2_-_DEF-REWRITE)
     :use (:instance
     V2-Moufang-law-2
     (z (V2_1))))))

(defthm
 V2_dot=V1_dot-1
 (implies (and (V1p x)
    (V1p y))
     (equal (V2_dot (cons x (V1_0))
        (cons y (V1_0)))
      (V1_dot x y))))

(defthm
 V2_dot=V1_dot-2
 (implies (and (V1p x)
    (V1p y))
     (equal (V2_dot (cons (V1_0) x)
        (cons (V1_0) y))
      (V1_dot x y))))

(defthm
 Dot-product-doubling
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V2_dot (cons u x)
        (cons y z))
      (+ (V1_dot u y)
         (V1_dot x z))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V2_DOT-DEF)
             Distributivity-V2_dot-V2_+-left&right)
     :use (:instance
     Distributivity-V2_dot-V2_+-left&right
     (a 1)
     (b 1)
     (c 1)
     (d 1)
     (u (cons u (V1_0)))
     (x (cons (V1_0) x))
     (y (cons y (V1_0)))
     (z (cons (V1_0) z))))))

(defthm
 Conjugation-doubling
 (implies (and (V1p x)
    (V1p y))
     (equal (V2_conjugate (cons x y))
      (cons (V1_conjugate x)
      (V1_- y))))
 :hints (("Goal"
     :in-theory (e/d ((:DEFINITION V2_1-def))
         ((:DEFINITION V1_DOT-DEF)
          (:DEFINITION V2_DOT-DEF))))))

(defthm
 V1_-V1_0=V1_0
 (equal (V1_- (V1_0))(V1_0))
 :hints (("Goal"
     :in-theory (disable V1_-_is-unique)
     :use (:instance
     V1_-_is-unique
     (x (V1_0))
     (y (V1_0))))))

(defthmD 
 V2_conjugate-cons-V1_0-V1p-lemma-a
 (implies (V1p x)
     (equal (V2_conjugate (V2_* (cons x (V1_0))
              (cons (V1_0)(V1_1))))
      (V2_conjugate (cons (V1_0) x))))
 :hints (("Goal"
     :in-theory (e/d (V1p*i=cons-V1_0-V1p)
         ((:DEFINITION V1_CONJUGATE))))))

(defthmD    
 V2_conjugate-cons-V1_0-V1p-lemma-b
 (implies (V1p x)
     (equal (V2_* (V2_conjugate (cons (V1_0)(V1_1)))
      (V2_conjugate (cons x (V1_0))))
      (V2_conjugate (V2_* (cons x (V1_0))
              (cons (V1_0)(V1_1))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)))))

(defthmD    
 V2_conjugate-cons-V1_0-V1p-lemma-c
 (implies (V1p x)
     (equal (V2_* (V2_conjugate (cons (V1_0)(V1_1)))
      (V2_conjugate (cons x (V1_0)))) 
      (V2_* (V2_- (cons (V1_0)(V1_1)))
      (cons (V1_conjugate x)(V1_0)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)))))

(defthmD    
 V2_conjugate-cons-V1_0-V1p-lemma-d
 (implies (V1p x)
     (equal (V2_* (V2_- (cons (V1_0)(V1_1)))
      (cons (V1_conjugate x)(V1_0))) 
      (V2_- (V2_* (cons (V1_0)(V1_1))
            (cons (V1_conjugate x)(V1_0))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             V2_-_DEF-REWRITE))))

(defthmD
 V2_-V2_*i-consV1_conjugateV1_0=V2_conjugate-cons-V1_0-V1p
 (implies (V1p x)
     (equal (V2_- (V2_* (cons (V1_0)(V1_1))
            (cons (V1_conjugate x)(V1_0))))
      (V2_conjugate (cons (V1_0) x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             V2_-_DEF-REWRITE
             CONJUGATION-DOUBLING)
     :use (V2_conjugate-cons-V1_0-V1p-lemma-a
     V2_conjugate-cons-V1_0-V1p-lemma-b
     V2_conjugate-cons-V1_0-V1p-lemma-c
     V2_conjugate-cons-V1_0-V1p-lemma-d))))

(defthmD  
 V2_-V2_conjugate-cons-V1_0-V1p=cons-V1_0-V1p
 (implies (V1p x)
     (equal (V2_- (V2_conjugate (cons (V1_0) x)))
      (cons (V1_0) x))))

(defthmD  
 V2_-V2_-V2_*i-consV1_conjugateV1_0=cons-V1_0-V1p
 (implies (V1p x)
     (equal (V2_- (V2_- (V2_* (cons (V1_0)(V1_1))
            (cons (V1_conjugate x)(V1_0)))))
      (cons (V1_0) x)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2P-DEF)
             V2_-_DEF-REWRITE
             CONJUGATION-DOUBLING)
     :use (V2_-V2_*i-consV1_conjugateV1_0=V2_conjugate-cons-V1_0-V1p
     V2_-V2_conjugate-cons-V1_0-V1p=cons-V1_0-V1p))))

(defthmD   
 V2_*i-consV1_conjugateV1_0=cons-V1_0-V1p
 (implies (V1p x)
     (equal (V2_* (cons (V1_0)(V1_1))
      (cons (V1_conjugate x)(V1_0)))
      (cons (V1_0) x)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_CONJUGATE)
             V2_-_DEF-REWRITE
             CONJUGATION-DOUBLING
             V2_-_V2_-_x=x)
     :use (V2_-V2_-V2_*i-consV1_conjugateV1_0=cons-V1_0-V1p
     (:instance
      V2_-_V2_-_x=x
      (x (V2_* (cons (V1_0)(V1_1))
         (cons (V1_conjugate x)(V1_0)))))))))

(defthmD
 V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-a
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot u (V2_* (cons x (V1_0))
          (V2_* (cons (V1_0)(V1_1))
          (cons (V1_conjugate y)(V1_0)))))
      (V2_dot u (V2_* (cons x (V1_0))
          (cons (V1_0) y)))))
 :hints (("Goal"
     :in-theory (e/d (V2_*i-consV1_conjugateV1_0=cons-V1_0-V1p)
         ((:DEFINITION V1_CONJUGATE)
          (:DEFINITION V2_DOT-DEF))))))

(defthmD
 V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-b
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot (V2_* (cons (V1_conjugate x)(V1_0))
        u)
        (V2_* (cons (V1_0)(V1_1))
        (cons (V1_conjugate y)(V1_0))))
      (V2_dot u (V2_* (cons x (V1_0))
          (V2_* (cons (V1_0)(V1_1))
          (cons (V1_conjugate y)(V1_0)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2_DOT-DEF)
             V2-Braid-Law-1)
     :use (:instance
     V2-Braid-Law-1
     (z u)
     (x (cons x (V1_0)))
     (y (V2_* (cons (V1_0)(V1_1))
        (cons (V1_conjugate y)(V1_0))))))))

(defthmD
 V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-c
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (- (V2_dot (V2_* (cons (V1_0)(V1_1))
           u)
           (V2_* (cons (V1_conjugate x)(V1_0))
           (cons (V1_conjugate y)(V1_0)))))
      (V2_dot (V2_* (cons (V1_conjugate x)(V1_0))
        u)
        (V2_* (cons (V1_0)(V1_1))
        (cons (V1_conjugate y)(V1_0))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2_DOT-DEF)
             V2-Exchange-Law)
     :use (:instance
     V2-Exchange-Law
     (u (cons (V1_conjugate x)(V1_0)))
     (x (cons (V1_0)(V1_1)))
     (y u)
     (z (cons (V1_conjugate y)(V1_0)))))))

(defthm
 V2_conjugate-i=V2_-i
 (equal (V2_conjugate (cons (V1_0)(V1_1)))
   (V2_- (cons (V1_0)(V1_1)))))

(defthmD
 V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-d
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (- (V2_dot u  
           (V2_* (V2_- (cons (V1_0)(V1_1))) 
           (V2_* (cons (V1_conjugate x)(V1_0))
           (cons (V1_conjugate y)(V1_0))))))
      (- (V2_dot (V2_* (cons (V1_0)(V1_1))
           u)
           (V2_* (cons (V1_conjugate x)(V1_0))
           (cons (V1_conjugate y)(V1_0)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2_DOT-DEF)
             V2-Braid-Law-1)
     :use (:instance
     V2-Braid-Law-1
     (x (cons (V1_0)(V1_1)))
     (y u)
     (z (V2_* (cons (V1_conjugate x)(V1_0))
        (cons (V1_conjugate y)(V1_0))))))))

(defthmD
 V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-e
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (- (V2_dot u  
           (V2_* (V2_- (cons (V1_0)(V1_1))) 
           (V2_* (cons (V1_conjugate x)(V1_0))
           (cons (V1_conjugate y)(V1_0))))))
      (V2_dot u  
        (V2_* (cons (V1_0)(V1_1)) 
        (V2_* (cons (V1_conjugate x)(V1_0))
              (cons (V1_conjugate y)(V1_0)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_DOT-DEF)
             V2_-_DEF-REWRITE
             Realp-V2_dot)
     :use (:instance
     Realp-V2_dot
     (x u)
     (y (V2_* (cons (V1_0)(V1_1)) 
        (V2_* (cons (V1_conjugate x)(V1_0))
              (cons (V1_conjugate y)(V1_0)))))))))

(defthmD
 V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-f
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot u  
        (V2_* (cons (V1_0)(V1_1)) 
        (V2_* (cons (V1_conjugate x)(V1_0))
              (cons (V1_conjugate y)(V1_0)))))
      (V2_dot u  
        (V2_* (cons (V1_0)(V1_1)) 
        (cons (V1_* (V1_conjugate x)
              (V1_conjugate y))
              (V1_0))))))
 :hints (("Goal"
     :in-theory (e/d (V2_*-cons=cons-V1_*)
         ((:DEFINITION V1_CONJUGATE)
          (:DEFINITION V2_DOT-DEF))))))

(defthmD
 V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-g
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot u  
        (V2_* (cons (V1_0)(V1_1)) 
        (cons (V1_* (V1_conjugate x)
              (V1_conjugate y))
              (V1_0))))
      (V2_dot u
        (cons (V1_0)(V1_* y x)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_DOT-DEF))
     :use (:instance
     V2_*i-consV1_conjugateV1_0=cons-V1_0-V1p
     (x (V1_* y x))))))

(defthm
 V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-h
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot u 
        (V2_* (cons x (V1_0))
        (cons (V1_0) y)))
      (V2_dot u
        (cons (V1_0)(V1_* y x)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_DOT-DEF)
             V2_-_DEF-REWRITE)
     :use (V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-a
     V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-b
     V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-c
     V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-d
     V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-e
     V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-f
     V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*-lemma-g))))

(defthm
 V2_*consV1pV1_0-consV1_0V1p=consV1_0V1_*
 (implies (and (V1p x)
    (V1p y))
     (equal (V2_* (cons x (V1_0))
      (cons (V1_0) y))
      (cons (V1_0)(V1_* y x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF))
     :use (:instance
     Forall-u-V2_dot-u-x=V2_dot-u-y->x=y
     (x (V2_* (cons x (V1_0))
        (cons (V1_0) y)))
     (y (cons (V1_0)(V1_* y x)))))))

(defthmD
 V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-a
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot u
        (V2_* (V2_* (cons (V1_0)(V1_1))
              (cons (V1_conjugate x)(V1_0)))
        (cons y (V1_0))))
      (V2_dot u
        (V2_* (cons (V1_0) x)
        (cons y (V1_0))))))
 :hints (("Goal"
     :in-theory (e/d (V2_*i-consV1_conjugateV1_0=cons-V1_0-V1p)
         ((:DEFINITION V1_CONJUGATE)
          (:DEFINITION V2_DOT-DEF))))))

(defthmD
 V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-b
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot u
        (V2_* (V2_* (cons (V1_0)(V1_1))
              (cons (V1_conjugate x)(V1_0)))
        (cons y (V1_0))))
      (V2_dot (V2_* u
        (cons (V1_conjugate y)
              (V1_0)))
        (V2_* (cons (V1_0)(V1_1))
        (cons (V1_conjugate x)(V1_0))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V1_CONJUGATE)
             V2-Braid-Law-2)
     :use (:instance
     V2-Braid-Law-2
     (z u)
     (x (V2_* (cons (V1_0)(V1_1))
        (cons (V1_conjugate x)(V1_0))))
     (y (cons y (V1_0)))))))

(defthmD
 V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-c
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot (V2_* u
        (cons (V1_conjugate y)
              (V1_0)))
        (V2_* (cons (V1_0)(V1_1))
        (cons (V1_conjugate x)(V1_0))))
      (V2_dot (V2_* u
        (cons (V1_conjugate y)
              (V1_0)))
        (V2_* (cons x (V1_0))
        (cons (V1_0)(V1_1))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V1_CONJUGATE)
             V2_*CONSV1PV1_0-CONSV1_0V1P=CONSV1_0V1_*)
     :use (V1p*i=cons-V1_0-V1p
     V2_*i-consV1_conjugateV1_0=cons-V1_0-V1p))))

(defthmD
 V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-d
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot (V2_* u
        (cons (V1_conjugate y)
              (V1_0)))
        (V2_* (cons x (V1_0))
        (cons (V1_0)(V1_1))))
      (- (V2_dot (V2_* u
           (cons (V1_0)(V1_1)))
           (V2_* (cons x (V1_0))
                                       (cons (V1_conjugate y)(V1_0)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2_DOT-DEF)
             V2-Exchange-Law)
     :use (:instance
     V2-Exchange-Law
     (x (cons x (V1_0)))
     (y (cons (V1_conjugate y)
        (V1_0)))
     (z (cons (V1_0)(V1_1)))))))

(defthmD
 V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-e
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (- (V2_dot (V2_* u
           (cons (V1_0)(V1_1)))
           (V2_* (cons x (V1_0))
           (cons (V1_conjugate y)(V1_0)))))
      (- (V2_dot u 
           (V2_* (V2_* (cons x (V1_0))
           (cons (V1_conjugate y)(V1_0)))
           (V2_- (cons (V1_0)(V1_1))))))))
     :hints (("Goal"
        :in-theory (disable (:DEFINITION V1_CONJUGATE)
          (:DEFINITION V2_CONJUGATE)
          (:DEFINITION V2_DOT-DEF)
          V2-Braid-Law-2)
        :use (:instance
        V2-Braid-Law-2
        (x u)
        (y (cons (V1_0)(V1_1)))
        (z (V2_* (cons x (V1_0))
           (cons (V1_conjugate y)(V1_0))))))))

(defthmD
 V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-f
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (- (V2_dot u 
           (V2_* (V2_* (cons x (V1_0))
           (cons (V1_conjugate y)(V1_0)))
           (V2_- (cons (V1_0)(V1_1))))))
      (V2_dot u 
        (V2_* (V2_* (cons x (V1_0))
              (cons (V1_conjugate y)(V1_0)))
        (cons (V1_0)(V1_1))))))
     :hints (("Goal"
        :in-theory (disable (:DEFINITION V1_CONJUGATE)
          (:DEFINITION V2_DOT-DEF)
          V2_-_DEF-REWRITE
          Realp-V2_dot)
        :use (:instance
        Realp-V2_dot
        (x u)
        (y (V2_* (V2_* (cons x (V1_0))
           (cons (V1_conjugate y)(V1_0)))
           (cons (V1_0)(V1_1))))))))

(defthmD
 V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-g
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot u 
        (V2_* (V2_* (cons x (V1_0))
              (cons (V1_conjugate y)(V1_0)))
        (cons (V1_0)(V1_1))))
      (V2_dot u
        (cons (V1_0)
        (V1_* x
              (V1_conjugate y))))))
     :hints (("Goal"
        :in-theory (e/d (V2_*-cons=cons-V1_*)
            ((:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_DOT-DEF))))))

(defthm
 V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-h
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot u
        (V2_* (cons (V1_0) x)
        (cons y (V1_0))))
      (V2_dot u
        (cons (V1_0)
        (V1_* x
              (V1_conjugate y))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2P-DEF)
             V2_-_DEF-REWRITE)
     :use (V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-a
     V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-b
     V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-c
     V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-d
     V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-e
     V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-f
     V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*-lemma-g))))

(defthm
 V2_*consV1_0V1p-consV1pV1_0=consV1_0V1_*
 (implies (and (V1p x)
    (V1p y))
     (equal (V2_* (cons (V1_0) x)
      (cons y (V1_0)))
      (cons (V1_0)
      (V1_* x
            (V1_conjugate y)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V1_CONJUGATE))
     :use (:instance
     Forall-u-V2_dot-u-x=V2_dot-u-y->x=y
     (x (V2_* (cons (V1_0) x)
        (cons y (V1_0))))
     (y (cons (V1_0)
        (V1_* x
        (V1_conjugate y))))))))

(defthmD
 V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-a
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot u
        (V2_* (cons (V1_0) x)
        (cons (V1_0) y)))
      (V2_dot u
        (V2_* (V2_* (cons (V1_0)(V1_1))
              (cons (V1_conjugate x)(V1_0)))
        (V2_* (cons (V1_0)(V1_1))
              (cons (V1_conjugate y)(V1_0)))))))
 :hints (("Goal"
     :in-theory (e/d (V2_*I-CONSV1_CONJUGATEV1_0=CONS-V1_0-V1P)
         ((:DEFINITION V1_CONJUGATE)
          (:DEFINITION V2_DOT-DEF))))))

(defthmD
 V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-b
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot u
        (V2_* (V2_* (cons (V1_0)(V1_1))
              (cons (V1_conjugate x)(V1_0)))
        (V2_* (cons (V1_0)(V1_1))
              (cons (V1_conjugate y)(V1_0)))))
      (V2_dot (V2_* u
        (V2_* (cons y (V1_0))
              (V2_- (cons (V1_0)(V1_1)))))
        (V2_* (cons (V1_0)(V1_1))
        (cons (V1_conjugate x)(V1_0))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V1_CONJUGATE)
             V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*-LEMMA-H
             V2_*CONSV1PV1_0-CONSV1_0V1P=CONSV1_0V1_*
             V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*
             V2-BRAID-LAW-2)
     :use (:instance
     V2-BRAID-LAW-2
     (z u)
     (x (V2_* (cons (V1_0)(V1_1))
        (cons (V1_conjugate x)(V1_0))))
     (y (V2_* (cons (V1_0)(V1_1))
        (cons (V1_conjugate y)(V1_0))))))))

(defthmD
 V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-c
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot (V2_* u
        (V2_* (cons y (V1_0))
              (V2_- (cons (V1_0)(V1_1)))))
        (V2_* (cons (V1_0)(V1_1))
        (cons (V1_conjugate x)(V1_0))))
      (- (V2_dot  (V2_* u
        (V2_* (cons y (V1_0))
              (cons (V1_0)(V1_1))))
        (V2_* (cons (V1_0)(V1_1))
        (cons (V1_conjugate x)(V1_0)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V1_CONJUGATE)
             V2_-_DEF-REWRITE
             V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*-LEMMA-H
             V2_*CONSV1PV1_0-CONSV1_0V1P=CONSV1_0V1_*
             V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*
             V2-BRAID-LAW-2))))

(defthmD
 V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-d
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (- (V2_dot  (V2_* u
            (V2_* (cons y (V1_0))
            (cons (V1_0)(V1_1))))
            (V2_* (cons (V1_0)(V1_1))
            (cons (V1_conjugate x)(V1_0)))))
       (- (V2_dot  (V2_* u
             (V2_* (cons (V1_0)(V1_1))
             (cons (V1_conjugate y)(V1_0))))
             (V2_* (cons (V1_0)(V1_1))
             (cons (V1_conjugate x)(V1_0)))))))

 :hints (("Goal"
     :in-theory (e/d (V1p*i=cons-V1_0-V1p
          V2_*i-consV1_conjugateV1_0=cons-V1_0-V1p)
         ((:DEFINITION V2_DOT-DEF)
          (:DEFINITION V2_CONJUGATE)
          (:DEFINITION V1_CONJUGATE)
          V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*-LEMMA-H
          V2_*CONSV1PV1_0-CONSV1_0V1P=CONSV1_0V1_*
          V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*)))))

(defthmD
 V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-e
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (- (V2_dot  (V2_* u
            (V2_* (cons (V1_0)(V1_1))
            (cons (V1_conjugate y)(V1_0))))
            (V2_* (cons (V1_0)(V1_1))
            (cons (V1_conjugate x)(V1_0)))))
      (V2_dot (V2_* u
        (cons (V1_conjugate x)(V1_0)))
        (V2_* (cons (V1_0)(V1_1))
        (V2_* (cons (V1_0)(V1_1))
              (cons (V1_conjugate y)(V1_0)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2_DOT-DEF)
             V2-Exchange-Law)
     :use (:instance
     V2-Exchange-Law
     (x (cons (V1_0)(V1_1)))
                (y (V2_* (cons (V1_0)(V1_1))
        (cons (V1_conjugate y)(V1_0))))
                (z (cons (V1_conjugate x)(V1_0)))))))

(defthmD
 V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-f
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot (V2_* u
        (cons (V1_conjugate x)(V1_0)))
        (V2_* (cons (V1_0)(V1_1))
        (V2_* (cons (V1_0)(V1_1))
              (cons (V1_conjugate y)(V1_0)))))
      (- (V2_dot (V2_* (cons (V1_0)(V1_1))
           (V2_* u
           (cons (V1_conjugate x)(V1_0))))
           (V2_* (cons (V1_0)(V1_1))
           (cons (V1_conjugate y)(V1_0)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2_DOT-DEF)
             V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*-LEMMA-H
             V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*
             V2-SCALING-LAW-LEFT
             V2-ALTERNATIVE-LAW-1
             V2_-_DEF-REWRITE
             V2-BRAID-LAW-1)
     :use (:instance
     V2-BRAID-LAW-1
     (x (cons (V1_0)(V1_1)))
     (y (V2_* (cons (V1_0)(V1_1))
        (cons (V1_conjugate y)(V1_0))))
     (z (V2_* u
        (cons (V1_conjugate x)(V1_0))))))))

(defthmD
 V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-g
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (- (V2_dot (V2_* (cons (V1_0)(V1_1))
           (V2_* u
           (cons (V1_conjugate x)(V1_0))))
           (V2_* (cons (V1_0)(V1_1))
           (cons (V1_conjugate y)(V1_0)))))
      (- (V2_dot (V2_* u
           (cons (V1_conjugate x)(V1_0)))
           (cons (V1_conjugate y)(V1_0))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2_DOT-DEF)
             V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*-LEMMA-H
             V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*
             V2-ALTERNATIVE-LAW-1
             V2_-_DEF-REWRITE))))

(defthmD
 V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-h
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (- (V2_dot (V2_* u
           (cons (V1_conjugate x)(V1_0)))
           (cons (V1_conjugate y)(V1_0))))
                 (- (V2_dot u
           (V2_* (cons (V1_conjugate y)(V1_0))
           (V2_conjugate (cons (V1_conjugate x)(V1_0))))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2_DOT-DEF)
             V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*-LEMMA-H
             V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*
             V2-ALTERNATIVE-LAW-1
             V2_-_DEF-REWRITE
             V2-BRAID-LAW-2)
     :use (:instance
     V2-BRAID-LAW-2
     (x u)
     (y (cons (V1_conjugate x)(V1_0)))
     (z (cons (V1_conjugate y)(V1_0)))))))

(defthmD
 V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-i
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (- (V2_dot u
           (V2_* (cons (V1_conjugate y)(V1_0))
           (V2_conjugate (cons (V1_conjugate x)(V1_0))))))
      (V2_dot u
        (V2_- (V2_* (cons (V1_conjugate y)(V1_0))
              (cons x (V1_0)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2_DOT-DEF)
             V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*-LEMMA-H
             V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*
             V2-ALTERNATIVE-LAW-1
             V2_-_DEF-REWRITE))))

(defthmD
 V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-j
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot u
        (V2_- (V2_* (cons (V1_conjugate y)(V1_0))
              (cons x (V1_0)))))
      (V2_dot u
        (cons (V1_- (V1_* (V1_conjugate y) x))
        (V1_0)))))
 :hints (("Goal"
     :in-theory (e/d (V2_*-cons=cons-V1_*)
         ((:DEFINITION V1_CONJUGATE)
          (:DEFINITION V2_CONJUGATE)
          (:DEFINITION V2_DOT-DEF)
          V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*-LEMMA-H
          V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*
          V2-ALTERNATIVE-LAW-1
          V1-BRAID-LAW-1
          DOT-PRODUCT-DOUBLING)))))

(defthm
 V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-k
 (implies (and (V2p u)
    (V1p x)
    (V1p y))
     (equal (V2_dot u
        (V2_* (cons (V1_0) x)
        (cons (V1_0) y)))
      (V2_dot u
        (cons (V1_- (V1_* (V1_conjugate y) x))
        (V1_0)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V2_CONJUGATE)
             (:DEFINITION V2_DOT-DEF)
             V2_-_DEF-REWRITE
             V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*-LEMMA-H
             V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*
             V2_*CONSV1PV1_0-CONSV1_0V1P=CONSV1_0V1_*
             V2-ALTERNATIVE-LAW-1
             V1-BRAID-LAW-1
             DOT-PRODUCT-DOUBLING
             CONJUGATION-DOUBLING
             V2-SCALING-LAW-LEFT)
     :use (V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-a
     V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-b
     V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-c
     V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-d
     V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-e
     V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-f
     V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-g
     V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-h
     V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-i
     V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*-lemma-j))))

(defthm
 V2_*consV1_0V1p-consV1_0V1p=consV1_-V1_*
 (implies (and (V1p x)
    (V1p y))
     (equal (V2_* (cons (V1_0) x)
      (cons (V1_0) y))
      (cons (V1_- (V1_* (V1_conjugate y) x))
      (V1_0))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_DOT-DEF)
             (:DEFINITION V1_CONJUGATE))
     :use (:instance
     Forall-u-V2_dot-u-x=V2_dot-u-y->x=y
     (x (V2_* (cons (V1_0) x)
        (cons (V1_0) y)))
     (y (cons (V1_- (V1_* (V1_conjugate y) x))
        (V1_0)))))))


(defthmD
 Product-doubling-lemma-a
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V2_* (cons u x)
      (cons y z))
      (V2_+ (V2_* (cons u (V1_0))
            (cons y z))
      (V2_* (cons (V1_0) x)
            (cons y z)))))
 :hints (("Goal"
     :in-theory (disable Right-Distributivity-V2_*_V2_+)
     :use (:instance 
     Right-Distributivity-V2_*_V2_+
     (z (cons y z))
     (a 1)
     (b 1)
     (x (cons u (V1_0)))
     (y (cons (V1_0) x))))))

(defthmD
 Product-doubling-lemma-b
 (implies (and (V1p u)
    (V1p y)
    (V1p z))
     (equal (V2_* (cons u (V1_0))
      (cons y z))
      (V2_+ (V2_* (cons u (V1_0))
            (cons y (V1_0)))
      (V2_* (cons u (V1_0))
            (cons (V1_0) z)))))
 :hints (("Goal"
     :in-theory (disable Left-Distributivity-V2_*_V2_+)
     :use (:instance
     Left-Distributivity-V2_*_V2_+
     (a 1)
     (b 1)
     (x (cons u (V1_0)))
     (y (cons y (V1_0)))
     (z (cons (V1_0) z))))))

(defthmD
 Product-doubling-lemma-c
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V2_* (cons (V1_0) x)
      (cons y z))
      (V2_+ (V2_* (cons (V1_0) x)
            (cons y (V1_0)))
      (V2_* (cons (V1_0) x)
            (cons (V1_0) z)))))
 :hints (("Goal"
     :in-theory (disable Left-Distributivity-V2_*_V2_+)
     :use (:instance
     Left-Distributivity-V2_*_V2_+
     (a 1)
     (b 1)
     (x (cons (V1_0) x))
     (y (cons y (V1_0)))
     (z (cons (V1_0) z))))))

(defthmD
 Product-doubling-lemma-d
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V2_+ (V2_* (cons u (V1_0))
            (cons y z))
      (V2_* (cons (V1_0) x)
            (cons y z)))
      (V2_+ (V2_* (cons u (V1_0))
            (cons y (V1_0)))
      (V2_+ (V2_* (cons u (V1_0))
            (cons (V1_0) z))
            (V2_+ (V2_* (cons (V1_0) x)
            (cons y (V1_0)))
            (V2_* (cons (V1_0) x)
            (cons (V1_0) z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_+-DEF))
     :use (Product-doubling-lemma-b
     Product-doubling-lemma-c))))

(defthmD
 Product-doubling-lemma-e
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V2_* (cons u x)
      (cons y z))
      (V2_+ (V2_* (cons u (V1_0))
            (cons y (V1_0)))
      (V2_+ (V2_* (cons u (V1_0))
            (cons (V1_0) z))
            (V2_+ (V2_* (cons (V1_0) x)
            (cons y (V1_0)))
            (V2_* (cons (V1_0) x)
            (cons (V1_0) z)))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_+-DEF))
     :use (Product-doubling-lemma-a
     Product-doubling-lemma-d))))

(defthm
 Product-doubling
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V2_* (cons u x)
      (cons y z))
      (cons (V1_+ (V1_* u y)
            (V1_- (V1_* (V1_conjugate z)
            x)))
      (V1_+ (V1_* z u)
            (V1_* x
            (V1_conjugate y))))))
 :hints (("Goal"
     :in-theory (e/d (V2_*-cons=cons-V1_*)
         ((:DEFINITION V1_conjugate)))
     :use Product-doubling-lemma-e)))

(in-theory (disable V2_*CONSV1PV1_0-CONSV1_0V1P=CONSV1_0V1_*
        V2_*CONSV1_0V1P-CONSV1PV1_0=CONSV1_0V1_*
        V2_*CONSV1_0V1P-CONSV1_0V1P=CONSV1_-V1_*))

(defthmD
 Norm-doubling-lemma
 (implies (and (V1p x)
    (V1p y))
     (equal (V2_norm (V2_+ (cons x (V1_0))
         (cons (V1_0) y)))
      (+ (V2_norm (cons x (V1_0)))
         (V2_norm (cons (V1_0) y))
         (* 2 (V2_dot (cons x (V1_0))
          (cons (V1_0) y))))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2_+-DEF)
             DOT-PRODUCT-DOUBLING
             Realp>=0-V2_norm
             V2_NORM=V1_NORM
             V1P-V1_0-ORTHOGONAL-V1_0-V1P)
     :use ((:instance
      Realp>=0-V2_norm
      (x (cons x (V1_0))))
     (:instance
      Realp>=0-V2_norm
      (x (cons (V1_0) y)))
     (:instance
      Realp>=0-V2_norm
      (x (V2_+ (cons x (V1_0))
         (cons (V1_0) y))))))))

(defthm
 Norm-doubling
 (implies (and (V1p x)
    (V1p y))
     (equal (V2_norm (cons x y))
      (+ (V1_norm x)
         (V1_norm y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V2P-DEF)
             (:DEFINITION V1_DOT-DEF)
             (:DEFINITION V2_DOT-DEF)
             DOT-PRODUCT-DOUBLING)
    :use Norm-doubling-lemma)))

(defthmD
 V1_norm-V1_-=V1_norm-lemma-a
 (implies (V1p x)
     (equal (V1_norm (V1_* (V1_- x)
         (V1_- x)))
      (V1_norm (V1_* x x)))))

(defthmD
 V1_norm-V1_-=V1_norm-lemma-b
 (implies (V1p x)
     (equal (* (V1_norm (V1_- x))
         (V1_norm (V1_- x)))
      (* (V1_norm x)
         (V1_norm x))))
 :hints (("Goal"
     :in-theory (disable V1_*-V1_-=V1_-V1_*-LEFT
             V1_*-V1_-=V1_-V1_*-RIGHT)
     :use V1_norm-V1_-=V1_norm-lemma-a)))

(defthmD
 V1_norm-V1_-=V1_norm-lemma-c
 (implies (and (real/rationalp a)
    (real/rationalp b))
     (equal (equal a b)
      (equal (- a b) 0))))

(defthmD
 V1_norm-V1_-=V1_norm-lemma-d
 (implies (and (real/rationalp a)
    (>= a 0)
    (real/rationalp b)
    (>= b 0))
     (equal (equal (* a a)(* b b))
      (equal a b)))
 :hints (("Goal"
     :in-theory (disable INVERSE-OF-+-AS=0)
     :use ((:instance
      V1_norm-V1_-=V1_norm-lemma-c
      (a (* a a))
      (b (* b b)))
     (:theorem
      (equal (- (* a a)(* b b))
       (* (+ a b)(- a b))))))))

(defthm
 V1_norm-V1_-=V1_norm
 (implies (V1p x)
     (equal (V1_norm (V1_- x))
      (V1_norm x)))
 :hints (("Goal"
     :use (V1_norm-V1_-=V1_norm-lemma-b
     (:instance
      V1_norm-V1_-=V1_norm-lemma-d
      (a (V1_norm (V1_- x)))
      (b (V1_norm x)))))))

(defthmD
 V1_*-associativity-lemma-a
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V2_norm (V2_* (cons y u)
         (cons z x)))
      (* (V2_norm (cons y u))
         (V2_norm (cons z x)))))
 :hints (("Goal"
     :in-theory (disable NORM-DOUBLING
             PRODUCT-DOUBLING))))

(defthmD
 V1_*-associativity-lemma-b
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V2_norm (cons (V1_+ (V1_* y z)
               (V1_- (V1_* (V1_conjugate x) u)))
         (V1_+ (V1_* x y)
               (V1_* u (V1_conjugate z)))))
      (* (V2_norm (cons y u))
         (V2_norm (cons z x)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             NORM-DOUBLING)
     :use V1_*-associativity-lemma-a)))

(defthmD
 V1_*-associativity-lemma-c
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (+ (V1_norm (V1_+ (V1_* y z)
            (V1_- (V1_* (V1_conjugate x) u))))
         (V1_norm (V1_+ (V1_* x y)
            (V1_* u (V1_conjugate z)))))
      (* (+ (V1_norm y)
      (V1_norm u))
         (+ (v1_norm z)
      (V1_norm x)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE))
     :use V1_*-associativity-lemma-b)))

(defthm
 V1_norm-V1_+=
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_norm (V1_+ x y))
      (+ (V1_norm x)
         (* 2 (V1_dot x y))
         (V1_norm y))))
 :hints (("Goal"
     :in-theory (disable Realp>=0-V1_norm)
     :use (Realp>=0-V1_norm
     (:instance
      Realp>=0-V1_norm
      (x y))
     (:instance
      Realp>=0-V1_norm
      (x (V1_+ x y)))))))

(defthmD
 V1_*-associativity-lemma-d
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (+ (V1_norm (V1_* y z))
         (- (* 2 (V1_dot (V1_* y z)  
             (V1_* (V1_conjugate x) u))))
         (V1_norm (V1_* (V1_conjugate x) u))
         (V1_norm (V1_* x y))
         (* 2 (V1_dot (V1_* x y)
          (V1_* u (V1_conjugate z))))
         (V1_norm (V1_* u (V1_conjugate z))))
      (+ (* (V1_norm y)
      (V1_norm z))
         (* (V1_norm y)
      (V1_norm x))
         (* (V1_norm u)
      (V1_norm z))
         (* (V1_norm u)
      (V1_norm x)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V1_DOT-DEF)
             V1-BRAID-LAW-1
             V1-BRAID-LAW-2)
     :use V1_*-associativity-lemma-c)))

(defthm
 Left-cancellation-for-+-a
 (implies (and (acl2-numberp x)
    (acl2-numberp y))
     (equal (equal (+ x y) x)
      (equal y 0))))

(defthmD
 V1_*-associativity-lemma-e
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot (V1_* x y)
        (V1_* u (V1_conjugate z)))
      (V1_dot (V1_* y z)  
        (V1_* (V1_conjugate x) u))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V1_DOT-DEF)
             Realp>=0-V1_norm
             Realp-V1_dot
             V1-BRAID-LAW-1
             V1-BRAID-LAW-2)
     :use (V1_*-associativity-lemma-d
     (:instance
      Realp>=0-V1_norm
      (x y))
     (:instance
      Realp>=0-V1_norm
      (x z))
     (:instance
      Realp-V1_dot
      (x (V1_* X Y))
      (y (V1_* U (V1_CONJUGATE Z))))
     (:instance
      Realp-V1_dot
      (x (V1_* Y Z))
      (y (V1_* (V1_CONJUGATE X) U)))))))

(defthm
 V1_*-associativity-lemma-f
 (implies (and (V1p u)
    (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_dot u
        (V1_* (V1_* x y) z))
      (V1_dot u
        (V1_* x (V1_* y z)))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             (:DEFINITION V1_DOT-DEF))
     :use V1_*-associativity-lemma-e)))

(defthm
 V1_*-associativity
 (implies (and (V1p x)
    (V1p y)
    (V1p z))
     (equal (V1_* (V1_* x y) z)
      (V1_* x (V1_* y z))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_DOT-DEF))
     :use (:instance
     Forall-u-V1_dot-u-x=V1_dot-u-y->x=y
     (x (V1_* (V1_* x y) z))
     (y (V1_* x (V1_* y z)))))))

(defthmD
 V1_*-commutativity-lemma-a
 (implies (and (V1p x)
    (V1p y))
     (equal (V2_* (V2_* (cons x (V1_0))
            (cons y (V1_0)))
      (cons (V1_0)(V1_1)))
      (cons (V1_0)(V1_* x y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             V1_*-ASSOCIATIVITY))))

(defthmD
 V1_*-commutativity-lemma-b
 (implies (and (V1p x)
    (V1p y))
     (equal (V2_* (cons x (V1_0))
      (V2_* (cons y (V1_0))
            (cons (V1_0)(V1_1))))
      (cons (V1_0)(V1_* y x))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION V1_CONJUGATE)
             V1_*-ASSOCIATIVITY))))

(defthm
 V1_*-commutativity
 (implies (and (V1p x)
    (V1p y))
     (equal (V1_* x y)
      (V1_* y x)))
 :hints (("Goal"
     :in-theory (e/d (V2_*-associativity)
         ((:DEFINITION V1_CONJUGATE)
          V1_*-ASSOCIATIVITY
          PRODUCT-DOUBLING))
     :use (V1_*-commutativity-lemma-a
     V1_*-commutativity-lemma-b))))

(defthmD
 V1_conjugate=identity-lemma
 (implies (V1p x)
     (equal (V2_* (cons (V1_0)(V1_1))
      (cons x (V1_0)))
      (cons (V1_0) (V1_conjugate x))))
 :hints (("Goal"
     :in-theory (disable (:definition V1_conjugate)))))

(defthm
 V1_conjugate=identity
 (implies (V1p x)
     (equal (V1_conjugate X)
      x))
 :hints (("Goal"
     :in-theory (e/d (V2_*-commutativity)
         ((:DEFINITION V1_CONJUGATE)
          PRODUCT-DOUBLING))
     :use (V1_conjugate=identity-lemma
     V1p*i=cons-V1_0-V1p))))