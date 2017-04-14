#|==========================================
 Cayley-Dickson Construction
   cayley1b.lisp

  31 March   2017

 Cons pairs of ACL2-numbers form a (4 dimensional) composition algebra.

   Real Composition Algebra:
     A Real Vector Algebra with Identity:
       A Real Vector Space with Multiplication
       and a Multiplicative Identity.
   The Vector Algebra also has a real valued Norm
       and a real valued Dot (or Inner) Product
       satisfying the Composition Law
          Norm(xy) = Norm(x)Norm(y).

   This algebra has a NON-trivial conjugate and 
   its multiplication is NOT commutative but  is 
   associative. Since the algebra satisfies the 
   Composition Law, the algebra has NO nontrivial 
   zero divisors.  All nonzero vectors have 
   multiplicative inverses.

   In fact, this algebra is (isomorphic to) the quaternions.

   3 Dimensional Vector Cross Product & 3 Dimensional Dot Product
   are related to 4 Dimensional Quaternion Multiplication.

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
(certify-book "cayley1b"
             0   ;; world with no commands  
             ) 
===============================
To use:
(include-book 
        "cayley1b"  
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
    "cayley1b.lisp")              ; read and evaluate each form in file 
==================|#

(in-package "ACL2")

(local
(include-book "arithmetic/top" :dir :system
         :uncertified-okp nil
         :defaxioms-okp nil
         :skip-proofs-okp nil))

(include-book "cayley1a"  
        :uncertified-okp nil
        :defaxioms-okp nil 
        :skip-proofs-okp nil) 

;;===============================
;;==Real Vector Space Operations:
;; Predicate for set of vectors
(defun
 4p (x)
 (and (consp x)
      (2p (car x))
      (2p (cdr x))))

;; Zero vector
(defun
 4_0 () 
 (cons (2_0)(2_0)))

;; Vector addition
(defun
 4_+ (x y) 
 (cons (2_+ (car x)(car y))
  (2_+ (cdr x)(cdr y))))

;; Vector minus
(defun
 4_- (x)
 (cons (2_- (car x))
  (2_- (cdr x))))

;; Scalar multiplication
(defun
 S4_* (a x)
 (cons (S2_* a (car x))
  (S2_* a (cdr x))))

;;================================================
;;==Vector Multiplication and Identity Operations:
;; Vector multiplication
(defun
 4_* (x y)
 (cons (2_+ (2_* (car x)
      (car y))
       (2_- (2_* (2_conjugate (cdr y))
           (cdr x))))
  (2_+ (2_* (cdr y) 
      (car x))
       (2_* (cdr x)
      (2_conjugate (car y))))))
;;----------------------------------------
(defun    ;; alternative definition
 4B_* (x y)
 (cons (2_+ (2_* (car x)
      (car y))
       (2_- (2_* (cdr y)
           (2_conjugate (cdr x)))))
  (2_+ (2_* (2_conjugate (car x))
      (cdr y))
       (2_* (car y)
      (cdr x)))))
;;-------------------------------------
;; One vector
(defun
 4_1 () 
 (cons (2_1)(2_0)))

;;=================
;;==Norm operation:
;; Vector Norm
(defun
 4_norm (x)
 (+ (2_norm (car x))
    (2_norm (cdr x))))

;;===================================
;;==Dot (or Inner) Product Operation:
;; Vector Dot Product
(defun
 4_dot (x y)
 (+ (2_dot (car x)(car y))
    (2_dot (cdr x)(cdr y))))

;;========================
;;==Conjugation Operation:
;; Vector conjugate
(defun
 4_conjugate (x)
 (cons (2_conjugate (car x))
  (2_- (cdr x))))

;;==========================
;; Real Vector Space Axioms:
(defthmD  
 4-Vector-closure
 (and (4p (4_0))
      (implies (and (4p x)
         (4p y))
    (4p (4_+ x y)))
      (implies (4p x)
    (4p (4_- x)))
      (implies (and (real/rationalp a)
         (4p x))
    (4p (S4_* a x)))))

(defthmD
 Associativity-of-4_+
 (implies (and (4p x)
    (4p y)
    (4p z))
     (equal (4_+ (4_+ x y) z)
      (4_+ x (4_+ y z)))))

(defthmD
 Commutativity-of-4_+
 (implies (and (4p x)
    (4p y))
     (equal (4_+ x y)
      (4_+ y x))))

(defthmD
 Unicity-of-4_0
 (implies (4p x)
     (equal (4_+ (4_0) x)
      x)))

(defthmD
 Inverse-of-4_+
 (implies (4p x)
     (equal (4_+ x (4_- x))
      (4_0))))

(defthmD
 Associativity-of-S4_*
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (4p x))
     (equal (S4_* a (S4_* b x))
      (S4_* (* a b) x))))

(defthmD
 Unicity-of-Scalar4-1
 (implies (4p x)
     (equal (S4_* 1 x) x)))

(defthmD
 Distributivity-S4_*-scalar-+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (4p x))
     (equal (S4_* (+ a b) x)
      (4_+ (S4_* a x)(S4_* b x)))))

(defthmD
 Distributivity-S4_*-4_+
 (implies (and (real/rationalp a)
    (4p x)
    (4p y))
     (equal (S4_* a (4_+ x y))
      (4_+ (S4_* a x)(S4_* a y)))))

;;=======================================
;; Additional Real Vector Algebra Axioms:
(defthmD
 4_1&4_*-closure
 (and (4p (4_1))
      (implies (and (4p x)
         (4p y))
    (4p (4_* x y)))))
;;------------------
(defthmD
 4B_*-closure
 (implies (and (4p x)
    (4p y))
     (4p (4B_* x y))))
;;----------------

(defthmD
 Not-4_1=4_0
 (not (equal (4_1)(4_0))))

(defthmD
 Left-Distributivity-4_*_4_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (4p x)
    (4p y)
    (4p z))
     (equal (4_* x 
           (4_+ (S4_* a y)
          (S4_* b z)))
      (4_+ (S4_* a
           (4_* x y))
           (S4_* b
           (4_* x z))))))
;;--------------------
(defthmD
 Left-Distributivity-4B_*_4_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (4p x)
    (4p y)
    (4p z))
     (equal (4B_* x 
      (4_+ (S4_* a y)
           (S4_* b z)))
      (4_+ (S4_* a
           (4B_* x y))
           (S4_* b
           (4B_* x z))))))
;;--------------

(defthmD
 Right-Distributivity-4_*_4_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (4p x)
    (4p y)
    (4p z))
     (equal (4_* (4_+ (S4_* a x)
          (S4_* b y))
           z)
      (4_+ (S4_* a
           (4_* x z))
           (S4_* b
           (4_* y z))))))
;;--------------
(defthmD
 Right-Distributivity-4B_*_4_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (4p x)
    (4p y)
    (4p z))
     (equal (4B_* (4_+ (S4_* a x)
           (S4_* b y))
      z)
      (4_+ (S4_* a
           (4B_* x z))
           (S4_* b
           (4B_* y z))))))
;;--------------

(defthmD
 Unicity-of-4_1
 (implies (4p x)
     (and (equal (4_* (4_1) x) x)
    (equal (4_* x (4_1)) x))))
;;-----------------
(defthmD
 4B_*-Unicity-of-4_1
 (implies (4p x)
     (and (equal (4B_* (4_1) x) x)
    (equal (4B_* x (4_1)) x))))
;;------------------
;;===============================================
;; Additional Vector Norm and Dot Product Axioms:
(defthmD
 Realp>=0-4_norm
 (implies (4p x)
     (and (real/rationalp (4_norm x))
    (>= (4_norm x) 0))))

(defthmD
 4_norm=0
 (implies (4p x)
     (equal (equal (4_norm x) 0)
      (equal x (4_0)))))

(defthmD
 4-Composition-Law
 (implies (and (4p x)
    (4p y))
     (equal (4_norm (4_* x y))
      (* (4_norm x)
         (4_norm y)))))
;;---------------------
(defthmD
 4B-Composition-Law
 (implies (and (4p x)
    (4p y))
     (equal (4_norm (4B_* x y))
      (* (4_norm x)
         (4_norm y)))))
;;-------------

(defthmD
 4_dot-def
 (equal (4_dot x y)
   (* 1/2 (+ (4_norm (4_+ x y))
       (- (4_norm x))
       (- (4_norm y)))))
 :rule-classes :definition)

(defthmD
 Distributivity-4_dot-4_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (4p x)
    (4p y)
    (4p z))
     (equal (4_dot (4_+ (S4_* a x)
            (S4_* b y))
       z)
      (+ (* a (4_dot x z))
         (* b (4_dot y z))))))

(defun-sk
 Forall-u-4_dot-u-x=0 (x)
 (forall (u)
    (implies (4p u)
       (equal (4_dot u x) 0)))
 :rewrite :direct)

(defthmD
 Forall-u-4_dot-u-x=0-def
 (equal (Forall-u-4_dot-u-x=0 x)
   (let ((u (Forall-u-4_dot-u-x=0-witness x)))
     (implies (4p u)
        (equal (4_dot u x) 0))))
 :rule-classes :definition)

;; redundant
(defthm
 Forall-u-4_dot-u-x=0-necc
 (implies (Forall-u-4_dot-u-x=0 x)
     (implies (4p u)
        (equal (4_dot u x) 0))))

(local   
(defthmD
  4_dot=0
  (implies (4p x)
      (equal (equal (4_dot x x) 0)
       (equal x (4_0))))))

(defthm  ;;4_dot is nonsingular
 Forall-u-4_dot-u-x=0->x=4_0
 (implies (and (4p x)
    (Forall-u-4_dot-u-x=0 x))
     (equal x (4_0)))
 :rule-classes nil
 :hints (("Goal"
     :in-theory (disable (:DEFINITION 4_DOT))
     :use 4_dot=0)))

(in-theory (disable Forall-u-4_dot-u-x=0-necc))

(defthmD
 4_conjugate-def-rewrite
 (implies (4p x)
     (equal (4_conjugate x)
      (4_+ (S4_* (* 2 (4_dot x (4_1)))
           (4_1))
           (4_- x)))))
;;=================================

(defthmD
 4_norm=2_norm
 (implies (2p x)
     (and (equal (4_norm (cons x (2_0)))
           (2_norm x))
    (equal (4_norm (cons (2_0) x))
           (2_norm x)))))

(defthmD  
 2p-2_0-orthogonal-2_0-2p
 (implies (and (2p x)
    (2p y))
     (equal (4_dot (cons x (2_0))
       (cons (2_0) y))
      0)))

(defthmD
 4_1-def 
 (equal (4_1)
   (cons (2_1)(2_0)))
 :rule-classes :definition)

(defthmD
 4_*-cons=cons-2_*
 (implies (and (2p x)
    (2p y))
     (equal (4_* (cons x (2_0))
           (cons y (2_0)))
      (cons (2_* x y)(2_0)))))
;;--------------
(defthmD
 4B_*-cons=cons-2_*
 (implies (and (2p x)
    (2p y))
     (equal (4B_* (cons x (2_0))
      (cons y (2_0)))
      (cons (2_* x y)(2_0)))))
;;---------------

(defthmD
 2p-4_*-i=cons-2_0-2p
 (implies (2p x)
     (equal (4_* (cons x (2_0))
           (cons (2_0)(2_1)))
      (cons (2_0) x))))
#|--------------------
(thm  
 ;;2p-4B_*-i=cons-2_0-2p
 (implies (2p x)
          (equal (4B_* (cons x (2_0))
                       (cons (2_0)(2_1)))
                 (cons (2_0) x))))
******** FAILED ********
-----------------------|#
(defthmD
 i-4B_*-2p=cons-2_0-2p
 (implies (2p x)
     (equal (4B_* (cons (2_0)(2_1))
      (cons x (2_0)))
      (cons (2_0) x))))
#|-------------------------
(thm
 ;;i-4_*-2p=cons-2_0-2p
 (implies (2p x)
          (equal (4_* (cons (2_0)(2_1))
                      (cons x (2_0)))
                 (cons (2_0) x))))
******** FAILED ********
----------------------|#
;;=========================
(defun
 4_/ (x)
 (S4_* (/ (4_norm x))
  (4_conjugate x)))

(defthmD
 4p-4_/
 (implies (and (4p x)
    (not (equal x (4_0))))
     (4p (4_/ x))))

(defthmD
 4_*-4_conjugate-right
 (implies (and (real/rationalp a)
    (not (equal a 0))
    (4p x))
     (equal (4_* x (S4_* (/ a)
             (4_conjugate x)))
      (S4_* (* (/ a)
         (4_norm x))
      (4_1)))))

(defthmD
 4_*-4_conjugate-left
 (implies (and (real/rationalp a)
    (not (equal a 0))
    (4p x))
     (equal (4_* (S4_* (/ a)
           (4_conjugate x))
      x)
      (S4_* (* (/ a)
         (4_norm x))
      (4_1)))))

(defthmD
 4_/=4_*-inverse-right
 (implies (and (4p x)
    (not (equal x (4_0))))
     (equal (4_* x (4_/ x))
      (4_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION |4P|)
             (:DEFINITION 4_*)
             (:DEFINITION S4_*)
             (:DEFINITION 4_NORM)
             (:DEFINITION 4_CONJUGATE)
             (:DEFINITION |4_1|)
             (:DEFINITION |4_0|)
             (:EXECUTABLE-COUNTERPART |4_1|)
             (:EXECUTABLE-COUNTERPART |4_0|))
     :use (Realp>=0-4_norm
     4_norm=0
     (:instance
      Unicity-of-Scalar4-1
      (x (4_1)))
     (:instance
      4_*-4_conjugate-right
      (a (4_norm x)))))))

(defthmD
 4_/=4_*-inverse-left
 (implies (and (4p x)
    (not (equal x (4_0))))
     (equal (4_* (4_/ x) x)
      (4_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION |4P|)
             (:DEFINITION 4_*)
             (:DEFINITION S4_*)
             (:DEFINITION 4_NORM)
             (:DEFINITION 4_CONJUGATE)
             (:DEFINITION |4_1|)
             (:DEFINITION |4_0|)
             (:EXECUTABLE-COUNTERPART |4_1|)
             (:EXECUTABLE-COUNTERPART |4_0|))
     :use (Realp>=0-4_norm
     4_norm=0
     (:instance
      Unicity-of-Scalar4-1
      (x (4_1)))
     (:instance
      4_*-4_conjugate-left
      (a (4_norm x)))))))
;;=============================
(defthmD
 4_conjugate-is-NOT-trivial
 (and (4p (cons (2_0)(2_1)))
      (not (equal (4_conjugate (cons (2_0)(2_1)))
       (identity (cons (2_0)(2_1)))))))

(defthmD
 4_*-is-NOT-commutative
 (let ((i (cons (cons 0 1)(2_0)))
  (j (cons (2_0)(2_1)))
  (k (cons (2_0)(cons 0 1))))
   (and (4p i)
   (4p j)
   (4p k)
   (equal (4_- k)
    (cons (2_0)(cons 0 -1)))
   (not (equal (4_- k)
         k))
   (equal (4_* i j) k)
   (equal (4_* j i)(4_- k))
   (not (equal (4_* i j)
         (4_* j i))))))
;;--------------------
(defthmD
 4B_*-is-NOT-commutative
 (let ((i (cons (cons 0 1)(2_0)))
  (j (cons (2_0)(2_1)))
  (k (cons (2_0)(cons 0 1))))
   (and (4p i)
   (4p j)
   (4p k)
   (equal (4_- k)
    (cons (2_0)(cons 0 -1)))
   (not (equal (4_- k)
         k))
   (equal (4B_* i j)(4_- k))
   (equal (4B_* j i) k)
   (not (equal (4B_* i j)
         (4B_* j i))))))
;;---------------

(defthmD
 4_*-is-associative
 (implies (and (4p x)
    (4p y)
    (4p z))
     (equal (4_* (4_* x y) z)
      (4_* x (4_* y z)))))
;;----------------------
(defthmD
 4B_*-is-associative
 (implies (and (4p x)
    (4p y)
    (4p z))
     (equal (4B_* (4B_* x y) z)
      (4B_* x (4B_* y z)))))
;;---------------------
(defthmD
 Not-4_*=4B_*
 (let ((i (cons (cons 0 1)(2_0)))
  (j (cons (2_0)(2_1))))
   (not (equal (4_*  i j)
    (4B_* i j)))))
;;------------------

(defthmD
 4_*=4B_*-reverse
 (implies (and (4p x)
    (4p y))
     (equal (4_*  x y)
      (4B_* y x))))
#|============================================
 Recall the definitions of 4_* and 4B_*
(defun
 4_* (x y)
 (cons (2_+ (2_* (car x)
      (car y))
       (2_- (2_* (2_conjugate (cdr y))
           (cdr x))))
  (2_+ (2_* (cdr y) 
      (car x))
       (2_* (cdr x)
      (2_conjugate (car y))))))

(defun    ;; alternative definition
 4B_* (x y)
 (cons (2_+ (2_* (car x)
      (car y))
       (2_- (2_* (cdr y)
           (2_conjugate (cdr x)))))
  (2_+ (2_* (2_conjugate (car x))
      (cdr y))
       (2_* (car y)
      (cdr x)))))
===================|#
;; Since 2_* is commutative, 
;;   the definitions of 4_* and 4B_* could be reformulated:
(defthmD
 4_*-commutative-rewrite
 (equal (4_* x y)
   (cons (2_+ (2_* (car x)(car y))
        (2_- (2_* (cdr x)
            (2_conjugate (cdr y)))))
         (2_+ (2_* (car x)(cdr y))
        (2_* (cdr x)(2_conjugate (car y)))))))

(defthmD
 4B_*-commutative-rewrite
 (equal (4B_* x y)
   (cons (2_+ (2_* (car x)(car y))
        (2_- (2_* (cdr y)
            (2_conjugate (cdr x)))))
         (2_+ (2_* (car y)(cdr x))
        (2_* (cdr y)(2_conjugate (car x)))))))
;; Since 2_conjugate is NOT trivial,
;;   removing the conjugates would change the multiplication: 
(defun
 4A_* (x y)
 (cons (2_+ (2_* (car x)(car y))
       (2_- (2_* (cdr x)(cdr y))))
  (2_+ (2_* (car x)(cdr y))
       (2_* (cdr x)(car y)))))

;; Using the original definitions of 4_* and 4B_*:
;;  The product of nonzero values is always nonzero.
;; With the alternative definition of 4A_*.
;;  the product of nonzero values could be zero.
(defthmD
 4A_*-zero-divisors
 (let ((x (cons (2_1)(cons 0  1)))
  (y (cons (2_1)(cons 0 -1))))
   (and (equal (4_*  x y)(cons (cons 2 0)(2_0)))
   (equal (4B_* x y)(cons (cons 2 0)(2_0)))
   (equal (4A_* x y)(4_0))
   (not (equal (4_*  x y)
         (4A_* x y)))
   (not (equal (4B_* x y)
         (4A_* x y))))))
;;=======================================
;; Quaternions can be construced from cons pairs of cons pairs of reals.
;;   What happens when this construction is applied to 
;;   pairs of pairs of complex numbers, in place of pairs of pairs of reals?

;; Apply 4_* and 4B_* to cons pairs of cons pairs of complex numbers 
;;  instead of cons pairs of cons pairs of real numbers:

;;  Using pairs of pairs of reals, the product of nonzero values is always nonzero.
;;  Using pairs of pairs of complex numbers, the product of nonzero values could be zero.
(defthm
 4_*&4B_*-complex-zero-divisors
 (let ((p1 (cons (complex 0 -1)(complex 0 0)))
  (p2 (cons (complex 1  0)(complex 0 0)))
  (p3 (cons (complex 0  1)(complex 0 0)))
  (p4 (cons (complex 1  0)(complex 0 0))))
   (and (equal (cons p1 p2)
    '((#C(0 -1) . 0) 1 . 0))
   (equal (cons p3 p4)
    '((#C(0  1) . 0) 1 . 0))
   (equal (4_* (cons p1 p2)
         (cons p3 p4))
    (4_0))
   (equal (4B_* (cons p1 p2)
          (cons p3 p4))
    (4_0))))
 :rule-classes nil)
;;===============================================
;; 4_conjugate is an isomorphism from 4p with 4_*
;;  onto 4p with 4B_*.

(defthmD
 4p-4_conjugate
 (implies (4p x)
     (4p (4_conjugate x))))

(defthm
 4_conjugate-is-1to1
 (implies (and (4p x)
    (4p y)
    (equal (4_conjugate x)
           (4_conjugate y)))
     (equal x y))
 :rule-classes nil)

(defthmD
 4_conjugate-is-onto
 (implies (4p x)
     (and (4p (4_conjugate x))
    (equal (4_conjugate (4_conjugate x))
           x))))

(defthmD
 4_conjugate-4_0
 (equal (4_conjugate (4_0))
   (4_0)))

(defthmD
 4_conjugate-4_1
 (equal (4_conjugate (4_1))
   (4_1)))

(defthmD
 4_conjugate-4_+
 (implies (and (4p x)
    (4p y))
     (equal (4_conjugate (4_+ x y))
      (4_+ (4_conjugate x)
           (4_conjugate y)))))

(defthmD
 4_conjugate-4_*
 (implies (and (4p x)
    (4p y))
     (equal (4_conjugate (4_* x y))
      (4B_* (4_conjugate x)
      (4_conjugate y)))))

(defthmD
 4_conjugate-S4_*
 (implies (and (real/rationalp a)
    (4p x))
     (equal (4_conjugate (S4_* a x))
      (S4_* a (4_conjugate x)))))

(defthmD
 4_conjugate-4_-
 (implies (4p x)
     (equal (4_conjugate (4_- x))
      (4_- (4_conjugate x)))))

(defthmD
 4_conjugate-4_/
 (implies (and (4p x)
    (not (equal x (4_0))))
     (equal (4_conjugate (4_/ x))
      (4_/ (4_conjugate x)))))
;;======================================
;;==Real Vector Space Operations:
;; Predicate for set of vectors
(defun
 3p (x)
 (and (consp x)
      (1p (car x))
      (2p (cdr x))))

;; Zero vector
(defun
 3_0 () 
 (cons (1_0)(2_0)))

;; Vector addition
(defun
 3_+ (x y) 
 (cons (1_+ (car x)(car y))
  (2_+ (cdr x)(cdr y))))

;; Vector minus
(defun
 3_- (x)
 (cons (1_- (car x))
  (2_- (cdr x))))

;; Scalar multiplication
(defun
 S3_* (a x)
 (cons (S1_* a (car x))
  (S2_* a (cdr x))))

;; Vector Norm
(defun
 3_norm (x)
 (+ (1_norm (car x))
    (2_norm (cdr x))))

;; Vector Dot Product
(defun
 3_dot (x y)
 (+ (1_dot (car x)(car y))
    (2_dot (cdr x)(cdr y))))

;; 3D Vector Cross Product
(defun     
 3_X (x y)
 (cons (+ (* (cadr x)
        (cddr y))
     (- (* (cddr x)
     (cadr y))))
  (cons (+ (* (cddr x)
        (car y))
     (- (* (car x)
           (cddr y))))
        (+ (* (car x)
        (cadr y))
     (- (* (cadr x)
           (car y)))))))
;;==========================
;; Real Vector Space Axioms:
(defthmD  
 3-Vector-closure
 (and (3p (3_0))
      (implies (and (3p x)
         (3p y))
    (3p (3_+ x y)))
      (implies (3p x)
    (3p (3_- x)))
      (implies (and (real/rationalp a)
         (3p x))
    (3p (S3_* a x)))))

(defthmD
 Associativity-of-3_+
 (implies (and (3p x)
    (3p y)
    (3p z))
     (equal (3_+ (3_+ x y) z)
      (3_+ x (3_+ y z)))))

(defthmD
 Commutativity-of-3_+
 (implies (and (3p x)
    (3p y))
     (equal (3_+ x y)
      (3_+ y x))))

(defthmD
 Unicity-of-3_0
 (implies (3p x)
     (equal (3_+ (3_0) x)
      x)))

(defthmD
 Inverse-of-3_+
 (implies (3p x)
     (equal (3_+ x (3_- x))
      (3_0))))

(defthmD
 Associativity-of-S3_*
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (3p x))
     (equal (S3_* a (S3_* b x))
      (S3_* (* a b) x))))

(defthmD
 Unicity-of-Scalar3-1
 (implies (3p x)
     (equal (S3_* 1 x) x)))

(defthmD
 Distributivity-S3_*-scalar-+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (3p x))
     (equal (S3_* (+ a b) x)
      (3_+ (S3_* a x)(S3_* b x)))))

(defthmD
 Distributivity-S3_*-3_+
 (implies (and (real/rationalp a)
    (3p x)
    (3p y))
     (equal (S3_* a (3_+ x y))
      (3_+ (S3_* a x)(S3_* a y)))))

;;===============================================
;; Additional Vector norm, Vector Cross and Dot Product Axioms:
(defthmD
 Realp>=0-3_norm
 (implies (3p x)
     (and (real/rationalp (3_norm x))
    (>= (3_norm x) 0))))

(defthmD
 3_norm=0
 (implies (3p x)
     (equal (equal (3_norm x) 0)
      (equal x (3_0)))))

(defthmD  
 3_dot&3_X-closure
 (implies (and (3p x)
    (3p y))
     (and (real/rationalp (3_dot x y))
    (3p (3_X x y)))))

(defthmD
 Distributivity-3_dot-3_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (3p x)
    (3p y)
    (3p z))
     (equal (3_dot (3_+ (S3_* a x)
            (S3_* b y))
       z)
      (+ (* a (3_dot x z))
         (* b (3_dot y z))))))

(defun-sk
 Forall-u-3_dot-u-x=0 (x)
 (forall (u)
    (implies (3p u)
       (equal (3_dot u x) 0)))
 :rewrite :direct)

(defthmD
 Forall-u-3_dot-u-x=0-def
 (equal (Forall-u-3_dot-u-x=0 x)
   (let ((u (Forall-u-3_dot-u-x=0-witness x)))
     (implies (3p u)
        (equal (3_dot u x) 0))))
 :rule-classes :definition)

;; redundant
(defthm
 Forall-u-3_dot-u-x=0-necc
 (implies (Forall-u-3_dot-u-x=0 x)
     (implies (3p u)
        (equal (3_dot u x) 0))))

(local   
(defthmD
  3_dot=0
  (implies (3p x)
      (equal (equal (3_dot x x) 0)
       (equal x (3_0))))))

(defthm  ;;3_dot is nonsingular
 Forall-u-3_dot-u-x=0->x=3_0
 (implies (and (3p x)
    (Forall-u-3_dot-u-x=0 x))
     (equal x (3_0)))
 :rule-classes nil
 :hints (("Goal"
     :in-theory (disable (:DEFINITION 3_DOT))
     :use 3_dot=0)))

(in-theory (disable Forall-u-3_dot-u-x=0-necc))

(defthm
 3_X-orthagonal-x&y
 (implies (and (3p x)
    (3p y))
     (and (equal (3_dot x (3_X x y)) 0)
    (equal (3_dot y (3_X x y)) 0))))

(defthmD
 3_X-is-NOT-commutative
 (let ((i (cons 1 (2_0)))
  (j (cons 0 (2_1))))
   (and (3p i)
   (3p j)
   (not (equal (3_X i j)
         (3_X j i))))))

(defthmD
 3_X-is-NOT-associative
 (let ((i (cons 1 (2_0)))
  (j (cons 0 (2_1))))
   (and (3p i)
   (3p j)
   (not (equal (3_X (3_X i i) j)
         (3_X i (3_X i j)))))))

(defthm
 3_X-is-nilpotent
 (implies (3p x)
     (equal (3_X x x)(3_0))))

(defthmD
 3_X-nullity-of-3_0
 (implies (3p x)
     (and (equal (3_X (3_0) x)(3_0))
    (equal (3_X x (3_0))(3_0)))))

(defthmD
 3_X-is-anticommutative
 (implies (and (3p x)
    (3p y))
     (and (equal (3_- (3_X x y))
           (3_X y x))
    (equal (3_X (3_- x) y)
           (3_X y x))
    (equal (3_X x (3_- y))
           (3_X y x)))))

(defthmD
 Distributivity-3_X-3_+-right
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (3p x)
    (3p y)
    (3p z))
     (equal (3_X (3_+ (S3_* a x)
          (S3_* b y))
           z)
      (3_+ (S3_* a (3_X x z))
           (S3_* b (3_X y z))))))

(defthmD
 Distributivity-3_X-3_+-left
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (3p x)
    (3p y)
    (3p z))
     (equal (3_X x
           (3_+ (S3_* a y)
          (S3_* b z)))
      (3_+ (S3_* a (3_X x y))
           (S3_* b (3_X x z))))))

(defthmD
 1_norm-3_dot+3_norm-3_X
 (implies (and (3p x)
    (3p y))
     (equal (+ (1_norm (3_dot x y))
         (3_norm (3_X x y)))
      (* (3_norm x)
         (3_norm y)))))
;;==============================

(defun
 4_RealPart (x)
 (caar x))

(defun
 4_VectorPart (x)
 (cons (cdar x)
  (cdr x)))

(defthmD
 Closure-4_Real&4_Vector-Part
 (implies (4p x)
     (and (real/rationalp (4_RealPart x))
    (3p (4_VectorPart x)))))

(defun
 Real&3p-to-4p (a x)
 (cons (cons a (car x))
  (cdr x)))

(defthmD
 4p-Real&3p-to-4p
 (implies (and (real/rationalp a)
    (3p x))
     (4p (Real&3p-to-4p a x))))

(defun
 3p-to-4p (x)
 (cons (cons 0 (car x))
  (cdr x)))

(defthmD
 4p-3p-to-4p
 (implies (3p x)
     (4p (3p-to-4p x))))

(defthmD
 4_*=3_dot-3_X
 (implies (and (3p x)
    (3p y))
     (equal (4_* (3p-to-4p x)
           (3p-to-4p y))
      (Real&3p-to-4p (- (3_dot x y))
         (3_X x y)))))
;;-----------------
(defthmD
 4B_*=3_dot-3_X
 (implies (and (3p x)
    (3p y))
     (equal (4B_* (3p-to-4p x)
      (3p-to-4p y))
      (Real&3p-to-4p (- (3_dot x y))
         (3_X y x)))))
;;---------------

(defthmD
 3_X=4_VectorPart-4_*
 (implies (and (3p x)
    (3p y))
     (equal (3_X x y)
      (4_VectorPart (S4_* 1/2 (4_+ (4_* (3p-to-4p x)
                (3p-to-4p y))
                 (4_- (4_* (3p-to-4p y)
               (3p-to-4p x)))))))))
;;----------------
(defthmD
 3_X=4_VectorPart-4B_*
 (implies (and (3p x)
    (3p y))
     (equal (3_X x y)
      (4_VectorPart (S4_* 1/2 (4_+ (4B_* (3p-to-4p y)
                 (3p-to-4p x))
                 (4_- (4B_* (3p-to-4p x)
                (3p-to-4p y)))))))))
;;--------------------

(defthmD
 3_dot=4_RealPart-4_*
 (implies (and (3p x)
    (3p y))
     (equal (3_dot x y)
      (4_RealPart (S4_* -1/2 (4_+ (4_* (3p-to-4p x)
               (3p-to-4p y))
                (4_* (3p-to-4p y)
               (3p-to-4p x))))))))
;;----------------------
(defthmD
 3_dot=4_RealPart-4B_*
 (implies (and (3p x)
    (3p y))
     (equal (3_dot x y)
      (4_RealPart (S4_* -1/2 (4_+ (4B_* (3p-to-4p x)
                (3p-to-4p y))
                (4B_* (3p-to-4p y)
                (3p-to-4p x))))))))
;;---------------------------
(defthmD
 3_X-3_X=4_VectorPart-4_*
 (implies (and (3p x)
    (3p y)
    (3p z))
     (equal (3_X x (3_X y z))
      (4_VectorPart (S4_* 1/2 (4_+ (4_* (3p-to-4p x)
                (4_* (3p-to-4p y)
               (3p-to-4p z)))
                 (4_- (4_* (3p-to-4p y)
               (4_* (3p-to-4p z)
                    (3p-to-4p x))))))))))
;;-------------------
(defthmD
 3_X-3_X=4_VectorPart-4B_*
 (implies (and (3p x)
    (3p y)
    (3p z))
     (equal (3_X x (3_X y z))
      (4_VectorPart (S4_* 1/2 (4_+ (4B_* (3p-to-4p x)
                 (4_* (3p-to-4p z)
                (3p-to-4p y)))
                 (4_- (4B_* (3p-to-4p y)
                (4_* (3p-to-4p x)
                     (3p-to-4p z))))))))))
;;--------------------------
(defthmD
 Grassman-identity
 (implies (and (3p x)
    (3p y)
    (3p z))
     (equal (3_X x (3_X y z))
      (3_+ (S3_* (3_dot x z) y)
           (3_- (S3_* (3_dot x y) z))))))

(defthmD
 Jacobi-identity
 (implies (and (3p x)
    (3p y)
    (3p z))
     (equal (3_+ (3_X x (3_X y z))
           (3_+ (3_X y (3_X z x))
          (3_X z (3_X x y))))
      (3_0))))

(defthmD
 3_dot-3_X=4_dot-4_*
 (implies (and (3p x)
    (3p y)
    (3p z))
     (equal (3_dot (3_X x y)
       z)
      (4_dot (4_* (3p-to-4p x)
            (3p-to-4p y))
       (3p-to-4p z)))))
;;------------------------
(defthm
 3_dot-3_X=4_dot-4B_*
 (implies (and (3p x)
    (3p y)
    (3p z))
     (equal (3_dot (3_X x y)
       z)
      (4_dot (4B_* (3p-to-4p y)
             (3p-to-4p x))
       (3p-to-4p z)))))
;;-------------------------
(defthmD
 Interchange-rule
 (implies (and (3p x)
    (3p y)
    (3p z))
     (equal (3_dot (3_X x y)
       z)
      (3_dot x 
       (3_X y z)))))

(defthmD
 3_norm-3_X=1
 (implies (and (3p x)
    (3p y)
    (equal (3_norm x) 1)
    (equal (3_norm y) 1)
    (equal (3_dot x y) 0))
     (equal (3_norm (3_X x y)) 1))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION 3_DOT)
             (:DEFINITION 3_NORM)
             (:DEFINITION |3_X|))
    :use 1_norm-3_dot+3_norm-3_X)))

(defthmD
 3_X-x-3_X-x-y
 (implies (and (3p x)
    (3p y))
     (equal (3_X x
           (3_X x y))
      (3_+ (S3_* (3_dot x y) x)
           (3_- (S3_* (3_norm x) y))))))