#|==========================================
 Cayley-Dickson Construction
   cayley1a.lisp

  31 March   2017

 Cons pairs of Reals form a (2 dimensional) composition algebra.

   Real Composition Algebra:
     A Real Vector Algebra with Identity:
       A Real Vector Space with Multiplication
       and a Multiplicative Identity.
   The Vector Algebra also has a real valued Norm
       and a real valued Dot (or Inner) Product
       satisfying the Composition Law
          Norm(xy) = Norm(x)Norm(y).

   This algebra has a NON-trivial conjugate and 
   its multiplication is commutative and 
   associative.  Since the algebra satisfies the
   Composition Law, the algebra has NO nontrivial 
   zero divisors.  All nonzero vectors have 
   multiplicative inverses.

   In fact, this algebra is (isomorphic to) the complex numbers.

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
(certify-book "cayley1a"
             0   ;; world with no commands  
             ) 
===============================
To use:
(include-book 
        "cayley1a"  
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
    "cayley1a.lisp")              ; read and evaluate each form in file 
==================|#

(in-package "ACL2")

(local
(include-book "arithmetic/top" :dir :system
         :uncertified-okp nil
         :defaxioms-okp nil
         :skip-proofs-okp nil))

(include-book "cayley1"  
        :uncertified-okp nil
        :defaxioms-okp nil 
        :skip-proofs-okp nil) 

;;===============================
;;==Real Vector Space Operations:
;; Predicate for set of vectors
(defun
 2p (x)
 (and (consp x)
      (1p (car x))
      (1p (cdr x))))

;; Zero vector
(defun
 2_0 () 
 (cons (1_0)(1_0)))

;; Vector addition
(defun
 2_+ (x y) 
 (cons (1_+ (car x)(car y))
  (1_+ (cdr x)(cdr y))))

;; Vector minus
(defun
 2_- (x)
 (cons (1_- (car x))
  (1_- (cdr x))))

;; Scalar multiplication
(defun
 S2_* (a x)
 (cons (S1_* a (car x))
  (S1_* a (cdr x))))

;;================================================
;;==Vector Multiplication and Identity Operations:
;; Vector multiplication
(defun
 2_* (x y)
 (cons (1_+ (1_* (car x)
      (car y))
       (1_- (1_* (1_conjugate (cdr y))
           (cdr x))))
  (1_+ (1_* (cdr y) 
      (car x))
       (1_* (cdr x)
      (1_conjugate (car y))))))

;; One vector
(defun
 2_1 () 
 (cons (1_1)(1_0)))

;;=================
;;==Norm operation:
;; Vector Norm
(defun
 2_norm (x)
 (+ (1_norm (car x))
    (1_norm (cdr x))))

;;===================================
;;==Dot (or Inner) Product Operation:
;; Vector Dot Product
(defun
 2_dot (x y)
 (+ (1_dot (car x)(car y))
    (1_dot (cdr x)(cdr y))))

;;========================
;;==Conjugation Operation:
;; Vector conjugate
(defun
 2_conjugate (x)
 (cons (1_conjugate (car x))
  (1_- (cdr x))))

;;==========================
;; Real Vector Space Axioms:
(defthmD  
 2-Vector-closure
 (and (2p (2_0))
      (implies (and (2p x)
         (2p y))
    (2p (2_+ x y)))
      (implies (2p x)
    (2p (2_- x)))
      (implies (and (real/rationalp a)
         (2p x))
    (2p (S2_* a x)))))

(defthmD
 Associativity-of-2_+
 (implies (and (2p x)
    (2p y)
    (2p z))
     (equal (2_+ (2_+ x y) z)
      (2_+ x (2_+ y z)))))

(defthmD
 Commutativity-of-2_+
 (implies (and (2p x)
    (2p y))
     (equal (2_+ x y)
      (2_+ y x))))

(defthmD
 Unicity-of-2_0
 (implies (2p x)
     (equal (2_+ (2_0) x)
      x)))

(defthmD
 Inverse-of-2_+
 (implies (2p x)
     (equal (2_+ x (2_- x))
      (2_0))))

(defthmD
 Associativity-of-S2_*
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (2p x))
     (equal (S2_* a (S2_* b x))
      (S2_* (* a b) x))))

(defthmD
 Unicity-of-Scalar2-1
 (implies (2p x)
     (equal (S2_* 1 x) x)))

(defthmD
 Distributivity-S2_*-scalar-+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (2p x))
     (equal (S2_* (+ a b) x)
      (2_+ (S2_* a x)(S2_* b x)))))

(defthmD
 Distributivity-S2_*-2_+
 (implies (and (real/rationalp a)
    (2p x)
    (2p y))
     (equal (S2_* a (2_+ x y))
      (2_+ (S2_* a x)(S2_* a y)))))

;;=======================================
;; Additional Real Vector Algebra Axioms:
(defthmD
 2_1&2_*-closure
 (and (2p (2_1))
      (implies (and (2p x)
         (2p y))
    (2p (2_* x y)))))

(defthmD
 Not-2_1=2_0
 (not (equal (2_1)(2_0))))

(defthmD
 Left-Distributivity-2_*_2_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (2p x)
    (2p y)
    (2p z))
     (equal (2_* x 
           (2_+ (S2_* a y)
          (S2_* b z)))
      (2_+ (S2_* a
           (2_* x y))
           (S2_* b
          (2_* x z))))))

(defthmD
 Right-Distributivity-2_*_2_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (2p x)
    (2p y)
    (2p z))
     (equal (2_* (2_+ (S2_* a x)
          (S2_* b y))
           z)
      (2_+ (S2_* a
           (2_* x z))
           (S2_* b
           (2_* y z))))))

(defthmD
 Unicity-of-2_1
 (implies (2p x)
     (and (equal (2_* (2_1) x) x)
    (equal (2_* x (2_1)) x))))

;;===============================================
;; Additional Vector Norm and Dot Product Axioms:
(defthmD
 Realp>=0-2_norm
 (implies (2p x)
     (and (real/rationalp (2_norm x))
    (>= (2_norm x) 0))))

(defthmD
 2_norm=0
 (implies (2p x)
     (equal (equal (2_norm x) 0)
      (equal x (2_0)))))

(defthmD
 2-Composition-Law
 (implies (and (2p x)
    (2p y))
     (equal (2_norm (2_* x y))
      (* (2_norm x)
         (2_norm y)))))

(defthmD
 2_dot-def
 (equal (2_dot x y)
   (* 1/2 (+ (2_norm (2_+ x y))
       (- (2_norm x))
       (- (2_norm y)))))
 :rule-classes :definition)

(defthmD
 Distributivity-2_dot-2_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (2p x)
    (2p y)
    (2p z))
     (equal (2_dot (2_+ (S2_* a x)
            (S2_* b y))
       z)
      (+ (* a (2_dot x z))
         (* b (2_dot y z))))))

(defun-sk
 Forall-u-2_dot-u-x=0 (x)
 (forall (u)
    (implies (2p u)
       (equal (2_dot u x) 0)))
 :rewrite :direct)

(defthmD
 Forall-u-2_dot-u-x=0-def
 (equal (Forall-u-2_dot-u-x=0 x)
   (let ((u (Forall-u-2_dot-u-x=0-witness x)))
     (implies (2p u)
        (equal (2_dot u x) 0))))
 :rule-classes :definition)

;; redundant
(defthm
 Forall-u-2_dot-u-x=0-necc
 (implies (Forall-u-2_dot-u-x=0 x)
     (implies (2p u)
        (equal (2_dot u x) 0))))

(local   
(defthmD
  2_dot=0
  (implies (2p x)
      (equal (equal (2_dot x x) 0)
       (equal x (2_0))))))

(defthm  ;;2_dot is nonsingular
 Forall-u-2_dot-u-x=0->x=2_0
 (implies (and (2p x)
    (Forall-u-2_dot-u-x=0 x))
     (equal x (2_0)))
 :rule-classes nil
 :hints (("Goal"
     :in-theory (disable (:DEFINITION 2_DOT))
     :use 2_dot=0)))

(in-theory (disable Forall-u-2_dot-u-x=0-necc))

(defthmD
 2_conjugate-def-rewrite
 (implies (2p x)
     (equal (2_conjugate x)
      (2_+ (S2_* (* 2 (2_dot x (2_1)))
           (2_1))
           (2_- x)))))
;;=================================

(defthmD
 2_norm=1_norm
 (implies (1p x)
     (and (equal (2_norm (cons x (1_0)))
           (1_norm x))
    (equal (2_norm (cons (1_0) x))
           (1_norm x)))))

(defthmD  
 1p-1_0-orthogonal-1_0-1p
 (implies (and (1p x)
    (1p y))
     (equal (2_dot (cons x (1_0))
       (cons (1_0) y))
      0)))

(defthmD
 2_1-def 
 (equal (2_1)
   (cons (1_1)(1_0)))
 :rule-classes :definition)

(defthmD
 2_*-cons=cons-1_*
 (implies (and (1p x)
    (1p y))
     (equal (2_* (cons x (1_0))
           (cons y (1_0)))
      (cons (1_* x y)(1_0)))))

(defthmD
 1p*i=cons-1_0-1p
 (implies (1p x)
     (equal (2_* (cons x (1_0))
           (cons (1_0)(1_1)))
      (cons (1_0) x))))
;;=============================
(defun
 2_/ (x)
 (S2_* (/ (2_norm x))
  (2_conjugate x)))

(defthmD
 2p-2_/
 (implies (and (2p x)
    (not (equal x (2_0))))
     (2p (2_/ x))))

(defthmD
 2_*-2_conjugate-right
 (implies (and (real/rationalp a)
    (not (equal a 0))
    (2p x))
     (equal (2_* x (S2_* (/ a)
             (2_conjugate x)))
      (S2_* (* (/ a)
         (2_norm x))
      (2_1)))))

(defthmD
 2_*-2_conjugate-left
 (implies (and (real/rationalp a)
    (not (equal a 0))
    (2p x))
     (equal (2_* (S2_* (/ a)
           (2_conjugate x))
           x)
      (S2_* (* (/ a)
         (2_norm x))
      (2_1)))))

(defthmD
 2_/=2_*-inverse-right
 (implies (and (2p x)
    (not (equal x (2_0))))
     (equal (2_* x (2_/ x))
      (2_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION |2P|)
             (:DEFINITION 2_*)
             (:DEFINITION S2_*)
             (:DEFINITION 2_NORM)
             (:DEFINITION 2_CONJUGATE)
             (:DEFINITION |2_1|)
             (:DEFINITION |2_0|)
             (:EXECUTABLE-COUNTERPART |2_1|)
             (:EXECUTABLE-COUNTERPART |2_0|))
     :use (Realp>=0-2_norm
     2_norm=0
     (:instance
      Unicity-of-Scalar2-1
      (x (2_1)))
     (:instance
      2_*-2_conjugate-right
      (a (2_norm x)))))))

(defthmD
 2_/=2_*-inverse-left
 (implies (and (2p x)
    (not (equal x (2_0))))
     (equal (2_* (2_/ x) x)
      (2_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION |2P|)
             (:DEFINITION 2_*)
             (:DEFINITION S2_*)
             (:DEFINITION 2_NORM)
             (:DEFINITION 2_CONJUGATE)
             (:DEFINITION |2_1|)
             (:DEFINITION |2_0|)
             (:EXECUTABLE-COUNTERPART |2_1|)
             (:EXECUTABLE-COUNTERPART |2_0|))
     :use (Realp>=0-2_norm
     2_norm=0
     (:instance
      Unicity-of-Scalar2-1
      (x (2_1)))
     (:instance
      2_*-2_conjugate-left
      (a (2_norm x)))))))
;;=============================
(defthmD
 2_*-commutative-rewrite
 (equal (2_* x y)
   (cons (1_+ (1_* (car x)(car y))
        (1_- (1_* (cdr x)
            (1_conjugate (cdr y)))))
         (1_+ (1_* (car x)(cdr y))
        (1_* (cdr x)(1_conjugate (car y)))))))

(defthmD
 2_*-commutative-conjugate-rewrite
 (equal (2_* x y)
   (cons (1_+ (1_* (car x)(car y))
        (1_- (1_* (cdr x)(cdr y))))
         (1_+ (1_* (car x)(cdr y))
        (1_* (cdr x)(car y))))))
;;==============================

(defthmD
 2_conjugate-is-NOT-trivial
 (and (2p (cons (1_0)(1_1)))
      (not (equal (2_conjugate (cons (1_0)(1_1)))
       (identity (cons (1_0)(1_1)))))))

(defthmD
 2_*-is-commutative
 (implies (and (2p x)
    (2p y))
     (equal (2_* x y)
      (2_* y x))))

(defthmD
 2_*-is-associative
 (implies (and (2p x)
    (2p y)
    (2p z))
     (equal (2_* (2_* x y) z)
      (2_* x (2_* y z)))))
;;============================================
(defun
 2p-to-ACL2-numberp (x)
 (complex (car x)(cdr x)))

(defthmD
 acl2-numberp-2p-to-ACL2-numberp 
 (implies (2p x)
     (acl2-numberp (2p-to-ACL2-numberp x))))

(defthm
 2p-to-ACL2-numberp-is-1to1
 (implies (and (2p x)
    (2p y)
    (equal (2p-to-ACL2-numberp x)
           (2p-to-ACL2-numberp y)))
     (equal x y))
 :rule-classes nil)

(defthmD
 2p-to-ACL2-numberp-is-onto
 (implies (acl2-numberp x)
     (and (2p (cons (realpart x)
        (imagpart x)))
    (equal (2p-to-ACL2-numberp (cons (realpart x)
             (imagpart x)))
           x))))

(defthmD
 2p-to-ACL2-numberp-2_0
 (equal (2p-to-ACL2-numberp (2_0))
   0))

(defthmD
 2p-to-ACL2-numberp-2_1
 (equal (2p-to-ACL2-numberp (2_1))
   1))

(defthmD
 complex-def-rewrite
 (implies (and (real/rationalp x)
    (real/rationalp y))
     (equal (complex x y)
      (+ x (* #C(0 1) y))))
 :hints (("Goal"
     :use COMPLEX-DEFINITION)))

(defthmD
 2p-to-ACL2-numberp-2_+
 (implies (and (2p x)
    (2p y))
     (equal (2p-to-ACL2-numberp (2_+ x y))
      (+ (2p-to-ACL2-numberp x)
         (2p-to-ACL2-numberp y))))
 :hints (("Goal"
     :in-theory (enable complex-def-rewrite)))) 

(defthmD
 2p-to-ACL2-numberp-2_*
 (implies (and (2p x)
    (2p y))
     (equal (2p-to-ACL2-numberp (2_* x y))
      (* (2p-to-ACL2-numberp x)
         (2p-to-ACL2-numberp y))))
 :hints (("Goal"
     :in-theory (enable complex-def-rewrite)))) 

(defthmD
 2p-to-ACL2-numberp-2_-
 (implies (2p x)
     (equal (2p-to-ACL2-numberp (2_- x))
      (- (2p-to-ACL2-numberp x))))
 :hints (("Goal"
     :in-theory (enable complex-def-rewrite)))) 

(defthmD
 conjugate-of-acl2-numberp
 (implies (acl2-numberp x)
     (equal (conjugate x)
      (complex (realpart x)
         (- (imagpart x))))))

(defthmD
 2p-to-ACL2-numberp-2_conjugate
 (implies (2p x)
     (equal (2p-to-ACL2-numberp (2_conjugate x))
      (conjugate (2p-to-ACL2-numberp x))))
 :hints (("Goal"
     :in-theory (enable conjugate-of-acl2-numberp))))
;;===========================================================
;; Complex numbers can be construced from cons pairs of reals.
;;   What happens when this construction is applied to 
;;   pairs of complex numbers, in place of pairs of reals?

;; Apply 2_* to cons pairs of complex numbers 
;;  instead of cons pairs of real numbers:

;;  Using pairs of reals, the product of nonzero values is always nonzero.
;;  Using pairs of complex numbers, the product of nonzero values could be zero.
(defthm
 2_*-complex-zero-divisors
 (let ((c1 (complex 1 0))
  (c2 (complex 0 1))
  (c3 (complex 1 0))
  (c4 (complex 0 -1)))
   (and (equal (cons c1 c2)
    '(1 . #C(0 1)))
   (equal (cons c3 c4)
    '(1 . #C(0 -1)))
   (equal (2_* (cons c1 c2)
         (cons c3 c4))
    (2_0))))
 :rule-classes nil)