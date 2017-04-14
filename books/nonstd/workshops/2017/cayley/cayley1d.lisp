#|==========================================
 Cayley-Dickson Construction
   cayley1d.lisp

  31 March   2017

 Cons pairs of Octonions form a (16 dimensional) algebra.

   A Real Vector Algebra with Identity:
       A Real Vector Space with Multiplication
       and a Multiplicative Identity.
   The Vector Algebra also has a real valued Norm
       and a real valued Dot (or Inner) Product.

   This algebra has a NON-trivial conjugate and 
   its multiplication is NOT commutative and 
   also NOT associative. The norm does NOT satisfy
   the Composition Law: Norm(xy) = Norm(x)Norm(y),
   because the algebra has nontrivial zero divisors.
   All nonzero vectors have multiplicative inverses.

   In fact, this algebra is (isomorphic to) the Sedenions.

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
(certify-book "cayley1d"
             0   ;; world with no commands  
             ) 
===============================
To use:
(include-book 
        "cayley1d"  
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
    "cayley1d.lisp")              ; read and evaluate each form in file 
==================|#

(in-package "ACL2")

(local
(include-book "arithmetic/top" :dir :system
         :uncertified-okp nil
         :defaxioms-okp nil
         :skip-proofs-okp nil))

(include-book "cayley1c"  
        :uncertified-okp nil
        :defaxioms-okp nil 
        :skip-proofs-okp nil) 

;;===============================
;;==Real Vector Space Operations:
;; Predicate for set of vectors
(defun
 16p (x)
 (and (consp x)
      (8p (car x))
      (8p (cdr x))))

;; Zero vector
(defun
 16_0 () 
 (cons (8_0)(8_0)))

;; Vector addition
(defun
 16_+ (x y) 
 (cons (8_+ (car x)(car y))
  (8_+ (cdr x)(cdr y))))

;; Vector minus
(defun
 16_- (x)
 (cons (8_- (car x))
  (8_- (cdr x))))

;; Scalar multiplication
(defun
 S16_* (a x)
 (cons (S8_* a (car x))
  (S8_* a (cdr x))))

;;================================================
;;==Vector Multiplication and Identity Operations:
;; Vector multiplication
(defun
 16_* (x y)
 (cons (8_+ (8_* (car x)
      (car y))
       (8_- (8_* (8_conjugate (cdr y))
           (cdr x))))
  (8_+ (8_* (cdr y) 
      (car x))
       (8_* (cdr x)
      (8_conjugate (car y))))))

;; One vector
(defun
 16_1 () 
 (cons (8_1)(8_0)))

;;=================
;;==Norm operation:
;; Vector Norm
(defun
 16_norm (x)
 (+ (8_norm (car x))
    (8_norm (cdr x))))

;;===================================
;;==Dot (or Inner) Product Operation:
;; Vector Dot Product
(defun
 16_dot (x y)
 (+ (8_dot (car x)(car y))
    (8_dot (cdr x)(cdr y))))

;;========================
;;==Conjugation Operation:
;; Vector conjugate
(defun
 16_conjugate (x)
 (cons (8_conjugate (car x))
  (8_- (cdr x))))

;;==========================
;; Real Vector Space Axioms:
(defthmD  
 16-Vector-closure
 (and (16p (16_0))
      (implies (and (16p x)
         (16p y))
    (16p (16_+ x y)))
      (implies (16p x)
    (16p (16_- x)))
      (implies (and (real/rationalp a)
         (16p x))
    (16p (S16_* a x)))))

(defthmD
 Associativity-of-16_+
 (implies (and (16p x)
    (16p y)
    (16p z))
     (equal (16_+ (16_+ x y) z)
      (16_+ x (16_+ y z)))))

(defthmD
 Commutativity-of-16_+
 (implies (and (16p x)
    (16p y))
     (equal (16_+ x y)
      (16_+ y x))))

(defthmD
 Unicity-of-16_0
 (implies (16p x)
     (equal (16_+ (16_0) x)
      x)))

(defthmD
 Inverse-of-16_+
 (implies (16p x)
     (equal (16_+ x (16_- x))
      (16_0))))

(defthmD
 Associativity-of-S16_*
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (16p x))
     (equal (S16_* a (S16_* b x))
      (S16_* (* a b) x))))

(defthmD
 Unicity-of-Scalar16-1
 (implies (16p x)
     (equal (S16_* 1 x) x)))

(defthmD
 Distributivity-S16_*-scalar-+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (16p x))
     (equal (S16_* (+ a b) x)
      (16_+ (S16_* a x)(S16_* b x)))))

(defthmD
 Distributivity-S16_*-16_+
 (implies (and (real/rationalp a)
    (16p x)
    (16p y))
     (equal (S16_* a (16_+ x y))
      (16_+ (S16_* a x)(S16_* a y)))))

;;=======================================
;; Additional Real Vector Algebra Axioms:
(defthmD
 16_1&16_*-closure
 (and (16p (16_1))
      (implies (and (16p x)
         (16p y))
    (16p (16_* x y)))))

(defthmD
 Not-16_1=16_0
 (not (equal (16_1)(16_0))))

(defthmD
 Left-Distributivity-16_*_16_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (16p x)
    (16p y)
    (16p z))
     (equal (16_* x 
      (16_+ (S16_* a y)
            (S16_* b z)))
      (16_+ (S16_* a
             (16_* x y))
      (S16_* b
             (16_* x z))))))

(defthmD
 Right-Distributivity-16_*_16_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (16p x)
    (16p y)
    (16p z))
     (equal (16_* (16_+ (S16_* a x)
            (S16_* b y))
      z)
      (16_+ (S16_* a
             (16_* x z))
      (S16_* b
             (16_* y z))))))

(defthmD
 Unicity-of-16_1
 (implies (16p x)
     (and (equal (16_* (16_1) x) x)
    (equal (16_* x (16_1)) x))))

;;===============================================
;; Additional Vector Norm and Dot Product Axioms:
(defthmD
 Realp>=0-16_norm
 (implies (16p x)
     (and (real/rationalp (16_norm x))
    (>= (16_norm x) 0))))

(defthmD
 16_norm=0
 (implies (16p x)
     (equal (equal (16_norm x) 0)
      (equal x (16_0)))))

#|===============================
 This is false because of zero divisors.
  See below for example.
(defthmD
 16-Composition-Law
 (implies (and (16p x)
    (16p y))
     (equal (16_norm (16_* x y))
      (* (16_norm x)
         (16_norm y)))))
===========================|#

(defthmD
 16_dot-def
 (equal (16_dot x y)
   (* 1/2 (+ (16_norm (16_+ x y))
       (- (16_norm x))
       (- (16_norm y)))))
 :rule-classes :definition)

(defthmD
 Distributivity-16_dot-16_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (16p x)
    (16p y)
    (16p z))
     (equal (16_dot (16_+ (S16_* a x)
        (S16_* b y))
        z)
      (+ (* a (16_dot x z))
         (* b (16_dot y z))))))

(defun-sk
 Forall-u-16_dot-u-x=0 (x)
 (forall (u)
    (implies (16p u)
       (equal (16_dot u x) 0)))
 :rewrite :direct)

(defthmD
 Forall-u-16_dot-u-x=0-def
 (equal (Forall-u-16_dot-u-x=0 x)
   (let ((u (Forall-u-16_dot-u-x=0-witness x)))
     (implies (16p u)
        (equal (16_dot u x) 0))))
 :rule-classes :definition)

;; redundant
(defthm
 Forall-u-16_dot-u-x=0-necc
 (implies (Forall-u-16_dot-u-x=0 x)
     (implies (16p u)
        (equal (16_dot u x) 0))))

(local   
(defthmD
  16_dot=0
  (implies (16p x)
      (equal (equal (16_dot x x) 0)
       (equal x (16_0))))))

(defthm  ;;16_dot is nonsingular
 Forall-u-16_dot-u-x=0->x=8_0
 (implies (and (16p x)
    (Forall-u-16_dot-u-x=0 x))
     (equal x (16_0)))
 :rule-classes nil
 :hints (("Goal"
     :in-theory (disable (:DEFINITION 16_DOT))
     :use 16_dot=0)))

(in-theory (disable Forall-u-16_dot-u-x=0-necc))

(defthmD
 16_conjugate-def-rewrite
 (implies (16p x)
     (equal (16_conjugate x)
      (16_+ (S16_* (* 2 (16_dot x (16_1)))
             (16_1))
      (16_- x)))))
;;=================================

(defthmD
 16_norm=8_norm
 (implies (8p x)
     (and (equal (16_norm (cons x (8_0)))
           (8_norm x))
    (equal (16_norm (cons (8_0) x))
           (8_norm x)))))

(defthmD  
 8p-8_0-orthogonal-8_0-8p
 (implies (and (8p x)
    (8p y))
     (equal (16_dot (cons x (8_0))
        (cons (8_0) y))
      0)))

(defthmD
 16_1-def 
 (equal (16_1)
   (cons (8_1)(8_0)))
 :rule-classes :definition)

(defthmD
 16_*-cons=cons-8_*
 (implies (and (8p x)
    (8p y))
     (equal (16_* (cons x (8_0))
      (cons y (8_0)))
      (cons (8_* x y)(8_0)))))

(defthmD
 8p*i=cons-8_0-8p
 (implies (8p x)
     (equal (16_* (cons x (8_0))
      (cons (8_0)(8_1)))
      (cons (8_0) x))))
;;=========================

(defun
 16_/ (x)
 (S16_* (/ (16_norm x))
   (16_conjugate x)))

(defthmD
 16p-16_/
 (implies (and (16p x)
    (not (equal x (16_0))))
     (16p (16_/ x))))

(defthmD
 16_*-16_conjugate-right
 (implies (and (real/rationalp a)
    (not (equal a 0))
    (16p x))
     (equal (16_* x (S16_* (/ a)
         (16_conjugate x)))
      (S16_* (* (/ a)
          (16_norm x))
       (16_1)))))

(defthmD
 16_*-16_conjugate-left
 (implies (and (real/rationalp a)
    (not (equal a 0))
    (16p x))
     (equal (16_* (S16_* (/ a)
             (16_conjugate x))
      x)
      (S16_* (* (/ a)
          (16_norm x))
       (16_1)))))

(defthmD
 16_/=16_*-inverse-right
 (implies (and (16p x)
    (not (equal x (16_0))))
     (equal (16_* x (16_/ x))
      (16_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION |16P|)
             (:DEFINITION 16_*)
             (:DEFINITION S16_*)
             (:DEFINITION 16_NORM)
             (:DEFINITION 16_CONJUGATE)
             (:DEFINITION |16_1|)
             (:DEFINITION |16_0|)
             (:EXECUTABLE-COUNTERPART |16_1|)
             (:EXECUTABLE-COUNTERPART |16_0|))
     :use (Realp>=0-16_norm
     16_norm=0
     (:instance
      Unicity-of-Scalar16-1
      (x (16_1)))
     (:instance
      16_*-16_conjugate-right
      (a (16_norm x)))))))

(defthmD
 16_/=16_*-inverse-left
 (implies (and (16p x)
    (not (equal x (16_0))))
     (equal (16_* (16_/ x) x)
      (16_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION |16P|)
             (:DEFINITION 16_*)
             (:DEFINITION S16_*)
             (:DEFINITION 16_NORM)
             (:DEFINITION 16_CONJUGATE)
             (:DEFINITION |16_1|)
             (:DEFINITION |16_0|)
             (:EXECUTABLE-COUNTERPART |16_1|)
             (:EXECUTABLE-COUNTERPART |16_0|))
     :use (Realp>=0-16_norm
     16_norm=0
     (:instance
      Unicity-of-Scalar16-1
      (x (16_1)))
     (:instance
      16_*-16_conjugate-left
      (a (16_norm x)))))))
;;=============================
(defthmD
 16_conjugate-is-NOT-trivial
 (and (16p (cons (8_0)(8_1)))
      (not (equal (16_conjugate (cons (8_0)(8_1)))
       (identity (cons (8_0)(8_1)))))))

(defthmD
 16_*-is-NOT-commutative
 (let ((i (cons (cons (cons (cons 0 1)(2_0))(4_0))(8_0))) 
  (j (cons (cons (cons (2_0)(2_1))(4_0))(8_0)))
  (k (cons (cons (cons (2_0)(cons 0 1))(4_0))(8_0))))
   (and (16p i)
   (16p j)
   (16p k)
   (equal (16_- k)
    (cons (cons (cons (2_0)(cons 0 -1))(4_0))(8_0)))
   (not (equal (16_- k)
         k))
   (equal (16_* i j) k)
   (equal (16_* j i)(16_- k))
   (not (equal (16_* i j)
         (16_* j i))))))

(defthmD
 16_*-is-NOT-associative
 (let ((e5 (cons (cons (4_0)(4_1))(8_0)))
  (e6 (cons (cons (4_0)(cons (cons 0 1)(2_0)))(8_0)))
  (e7 (cons (cons (4_0)(cons (2_0)(2_1)))(8_0)))
  (e8 (cons (cons (4_0)(cons (2_0)(cons 0 1)))(8_0))))
   (and (16p e5)
   (16p e6)
   (16p e7)
   (16p e8)
   (equal (16_- e8)
    (cons (cons (4_0)(cons (2_0)(cons 0 -1)))(8_0)))
   (not (equal (16_- e8)
         e8))
   (equal (16_* (16_* e5 e6) e7)
    (16_- e8))
   (equal (16_* e5 (16_* e6 e7))
    e8)
   (not (equal (16_* (16_* e5 e6) e7)
         (16_* e5 (16_* e6 e7)))))))

;; The 16_* product of nonzero values could be zero.
;;   Thus the Composition Law: Norm(xy) = Norm(x)Norm(y),
;;   does not hold 
(defthmD
 16_*-zero-divisors
 (let ((x (cons (cons (cons (2_0)(cons 0 1))(4_0))
     (cons (cons (2_0)(2_1))(4_0))))
  (y (cons (cons (4_0)(cons (2_0)(2_1)))
     (cons (4_0)(cons (2_0)(cons 0 -1))))))
   (and (16p x)
   (16p y)
   (equal (16_* x y)(16_0))
   (not (equal (16_norm (16_* x y))
         (* (16_norm x)(16_norm y)))))))