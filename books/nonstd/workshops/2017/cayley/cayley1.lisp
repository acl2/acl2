#|==========================================
 Cayley-Dickson Construction
   cayley1.lisp

  31 March   2017

 The Reals form a (1 dimensional) composition algebra.

   Real Composition Algebra:
     A Real Vector Algebra with Identity:
       A Real Vector Space with Multiplication
       and a Multiplicative Identity.
   The Vector Algebra also has a real valued Norm
       and a real valued Dot (or Inner) Product
       satisfying the Composition Law
          Norm(xy) = Norm(x)Norm(y).

   This algebra has a trivial conjugate and 
   its multiplication is commutative and 
   associative.  Since the algebra satisfies
   the Composition Law, the algebra has NO 
   nontrivial zero divisors.  All nonzero vectors 
   have multiplicative inverses.

 References:

 J.H. Conway and D.A. Smith, On Quaternions and Octonions: Their Geometry,
 Arithmetic, and Symmetry, A K Peters, 2003, pages 67--73.

 H.-D. Ebbinghaus, H. Hermes, F. Hirzebruch, M. Koecher, K. Mainzer, 
 J. Neukirch, A. Prestel, and R. Remmert, Numbers, Springer, 1991, pp 256--261,
                                                                      265--274     

ACL2 Version 7.4(r) built March 30, 2017  08:51:54.
System books directory "/home/acl2/acl2-7.4r/acl2-7.4/books/".
ACL2 Version 7.4 built March 29, 2017  10:38:07.
System books directory "/home/acl2/acl2-7.4/acl2-7.4/books/".
===============================|#
#|====================================
To certify:
(certify-book "cayley1"
             0   ;; world with no commands  
             ) 
===============================
To use:
(include-book 
        "cayley1"  
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
    "cayley1.lisp")              ; read and evaluate each form in file 
==================|#

(in-package "ACL2")

(local
(include-book "arithmetic/top" :dir :system
         :uncertified-okp nil
         :defaxioms-okp nil
         :skip-proofs-okp nil))

;;===============================
;;==Real Vector Space Operations:
;; Predicate for set of vectors
(defun  
 1p (x)
 (real/rationalp x))

;; Zero vector
(defun
 1_0 ()
 0)

;; Vector addition
(defun
 1_+ (x y)
 (+ x y))

;; Vector minus
(defun
 1_- (x)
 (- x))

;; Scalar multiplication
(defun
 S1_* (a x)
 (* a x))

;;================================================
;;==Vector Multiplication and Identity Operations:
;; Vector multiplication
(defun
 1_* (x y)
 (* x y))

;; One vector
(defun
 1_1 ()
 1)

;;=================
;;==Norm operation:
;; Vector Norm
(defun
 1_norm (x)
 (* x x))

;;===================================
;;==Dot (or Inner) Product Operation:
;; Vector Dot Product
(defun
 1_dot (x y)
 (* x y))

;;========================
;;==Conjugation Operation:
;; Vector conjugate
(defun
 1_conjugate (x)
 (identity x))

;;==========================
;; Real Vector Space Axioms:
(defthmD  
 1-Vector-closure
 (and (1p (1_0))
      (implies (and (1p x)
         (1p y))
    (1p (1_+ x y)))
      (implies (1p x)
    (1p (1_- x)))
      (implies (and (real/rationalp a)
         (1p x))
    (1p (S1_* a x)))))

(defthmD
 Associativity-of-1_+
 (implies (and (1p x)
    (1p y)
    (1p z))
     (equal (1_+ (1_+ x y) z)
      (1_+ x (1_+ y z)))))

(defthmD
 Commutativity-of-1_+
 (implies (and (1p x)
    (1p y))
     (equal (1_+ x y)
      (1_+ y x))))

(defthmD
 Unicity-of-1_0
 (implies (1p x)
     (equal (1_+ (1_0) x)
      x)))

(defthmD
 Inverse-of-1_+
 (implies (1p x)
     (equal (1_+ x (1_- x))
      (1_0))))

(defthmD
 Associativity-of-S1_*
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (1p x))
     (equal (S1_* a (S1_* b x))
      (S1_* (* a b) x))))

(defthmD
 Unicity-of-Scalar1-1
 (implies (1p x)
     (equal (S1_* 1 x) x)))

(defthmD
 Distributivity-S1_*-scalar-+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (1p x))
     (equal (S1_* (+ a b) x)
      (1_+ (S1_* a x)(S1_* b x)))))

(defthmD
 Distributivity-S1_*-1_+
 (implies (and (real/rationalp a)
    (1p x)
    (1p y))
     (equal (S1_* a (1_+ x y))
      (1_+ (S1_* a x)(S1_* a y)))))

;;=======================================
;; Additional Real Vector Algebra Axioms:
(defthmD
 1_1&1_*-closure
 (and (1p (1_1))
      (implies (and (1p x)
         (1p y))
    (1p (1_* x y)))))

(defthmD
 Not-1_1=1_0
 (not (equal (1_1)(1_0))))

(defthmD
 Left-Distributivity-1_*_1_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (1p x)
    (1p y)
    (1p z))
     (equal (1_* x 
           (1_+ (S1_* a y)
          (S1_* b z)))
      (1_+ (S1_* a
           (1_* x y))
           (S1_* b
          (1_* x z))))))

(defthmD
 Right-Distributivity-1_*_1_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (1p x)
    (1p y)
    (1p z))
     (equal (1_* (1_+ (S1_* a x)
          (S1_* b y))
           z)
      (1_+ (S1_* a
           (1_* x z))
           (S1_* b
           (1_* y z))))))

(defthmD
 Unicity-of-1_1
 (implies (1p x)
     (and (equal (1_* (1_1) x) x)
    (equal (1_* x (1_1)) x))))

;;===============================================
;; Additional Vector Norm and Dot Product Axioms:
(defthmD
 Realp>=0-1_norm
 (implies (1p x)
     (and (real/rationalp (1_norm x))
    (>= (1_norm x) 0))))

(defthmD
 1_norm=0
 (implies (1p x)
     (equal (equal (1_norm x) 0)
      (equal x (1_0)))))

(defthmD
 1-Composition-Law
 (implies (and (1p x)
    (1p y))
     (equal (1_norm (1_* x y))
      (* (1_norm x)
         (1_norm y)))))

(defthmD
 1_dot-def
 (equal (1_dot x y)
   (* 1/2 (+ (1_norm (1_+ x y))
       (- (1_norm x))
       (- (1_norm y)))))
 :rule-classes :definition)

(defthmD
 Distributivity-1_dot-1_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (1p x)
    (1p y)
    (1p z))
     (equal (1_dot (1_+ (S1_* a x)
            (S1_* b y))
       z)
      (+ (* a (1_dot x z))
         (* b (1_dot y z))))))

(defun-sk
 Forall-u-1_dot-u-x=0 (x)
 (forall (u)
    (implies (1p u)
       (equal (1_dot u x) 0)))
 :rewrite :direct)

(defthmD
 Forall-u-1_dot-u-x=0-def
 (equal (Forall-u-1_dot-u-x=0 x)
   (let ((u (Forall-u-1_dot-u-x=0-witness x)))
     (implies (1p u)
        (equal (1_dot u x) 0))))
 :rule-classes :definition)

;; redundant
(defthm
 Forall-u-1_dot-u-x=0-necc
 (implies (Forall-u-1_dot-u-x=0 x)
     (implies (1p u)
        (equal (1_dot u x) 0))))

(local   
(defthmD
  1_dot=0
  (implies (1p x)
      (equal (equal (1_dot x x) 0)
       (equal x (1_0))))))

(defthm  ;;1_dot is nonsingular
 Forall-u-1_dot-u-x=0->x=1_0
 (implies (and (1p x)
    (Forall-u-1_dot-u-x=0 x))
     (equal x (1_0)))
 :rule-classes nil
 :hints (("Goal"
     :in-theory (disable (:DEFINITION 1_DOT))
     :use 1_dot=0)))

(in-theory (disable Forall-u-1_dot-u-x=0-necc))

(defthmD
 1_conjugate-def-rewrite
 (implies (1p x)
     (equal (1_conjugate x)
      (1_+ (S1_* (* 2 (1_dot x (1_1)))
           (1_1))
           (1_- x)))))
;;=================================
(defun
 1_/ (x)
 (S1_* (/ (1_norm x))
  (1_conjugate x)))

(defthmD
 1p-1_/
 (implies (and (1p x)
    (not (equal x (1_0))))
     (1p (1_/ x))))

(defthmD
 1_/=1_*-inverse-right
 (implies (and (1p x)
    (not (equal x (1_0))))
     (equal (1_* x (1_/ x))
      (1_1))))

(defthmD
 1_/=1_*-inverse-left
 (implies (and (1p x)
    (not (equal x (1_0))))
     (equal (1_* (1_/ x) x)
      (1_1))))
;;=============================
(defthmD
 1_conjugate-is-trivial
 (equal (1_conjugate x)
   (identity x)))

(defthmD
 1_*-is-commutative
 (implies (and (1p x)
    (1p y))
     (equal (1_* x y)
      (1_* y x))))

(defthmD
 1_*-is-associative
 (implies (and (1p x)
    (1p y)
    (1p z))
     (equal (1_* (1_* x y) z)
      (1_* x (1_* y z)))))