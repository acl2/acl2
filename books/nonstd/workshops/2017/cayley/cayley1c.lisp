#|==========================================
 Cayley-Dickson Construction
   cayley1c.lisp

  31 March   2017

 Cons pairs of Quaternions form a (8 dimensional) composition algebra.

   Real Composition Algebra:
     A Real Vector Algebra with Identity:
       A Real Vector Space with Multiplication
       and a Multiplicative Identity.
   The Vector Algebra also has a real valued Norm
       and a real valued Dot (or Inner) Product
       satisfying the Composition Law
          Norm(xy) = Norm(x)Norm(y).

   This algebra has a NON-trivial conjugate and 
   its multiplication is NOT commutative and 
   also NOT associative. Since the algebra satisfies
   the Composition Law, the algebra has NO nontrivial 
   zero divisors.  All nonzero vectors have multiplicative 
   inverses.

   In fact, this algebra is (isomorphic to) the Octonions.

   7 Dimensional Vector Cross Product & 7 Dimensional Dot Product
   are related to 8 Dimensional Octonion Multiplication.

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
(certify-book "cayley1c"
             0   ;; world with no commands  
             ) 
===============================
To use:
(include-book 
        "cayley1c"  
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
    "cayley1c.lisp")              ; read and evaluate each form in file 
==================|#

(in-package "ACL2")

(local
(include-book "arithmetic/top" :dir :system
         :uncertified-okp nil
         :defaxioms-okp nil
         :skip-proofs-okp nil))

(local
(in-theory (disable default-+-2)))

(include-book "cayley1b"  
        :uncertified-okp nil
        :defaxioms-okp nil 
        :skip-proofs-okp nil) 

;;===============================
;;==Real Vector Space Operations:
;; Predicate for set of vectors
(defun
 8p (x)
 (and (consp x)
      (4p (car x))
      (4p (cdr x))))

;; Zero vector
(defun
 8_0 () 
 (cons (4_0)(4_0)))

;; Vector addition
(defun
 8_+ (x y) 
 (cons (4_+ (car x)(car y))
  (4_+ (cdr x)(cdr y))))

;; Vector minus
(defun
 8_- (x)
 (cons (4_- (car x))
  (4_- (cdr x))))

;; Scalar multiplication
(defun
 S8_* (a x)
 (cons (S4_* a (car x))
  (S4_* a (cdr x))))

;;================================================
;;==Vector Multiplication and Identity Operations:
;; Vector multiplication
(defun
 8_* (x y)
 (cons (4_+ (4_* (car x)
      (car y))
       (4_- (4_* (4_conjugate (cdr y))
           (cdr x))))
  (4_+ (4_* (cdr y) 
      (car x))
       (4_* (cdr x)
      (4_conjugate (car y))))))
;;----------------------------------------
(defun    ;; alternative definition B.
 8B_* (x y)
 (cons (4_+ (4B_* (car x)
       (car y))
       (4_- (4B_* (cdr y)
      (4_conjugate (cdr x)))))
  (4_+ (4B_* (4_conjugate (car x))
       (cdr y))
       (4B_* (car y)
       (cdr x)))))

(defun    ;; alternative definition C.
 8C_* (x y)
 (cons (4_+ (4_* (car x)
      (car y))
       (4_- (4_* (cdr y)
           (4_conjugate (cdr x)))))
  (4_+ (4_* (4_conjugate (car x))
      (cdr y))
       (4_* (car y)
      (cdr x)))))

(defun   ;; alternative definition D.
 8D_* (x y)
 (cons (4_+ (4B_* (car x)
       (car y))
       (4_- (4B_* (4_conjugate (cdr y))
      (cdr x))))
  (4_+ (4B_* (cdr y) 
       (car x))
       (4B_* (cdr x)
       (4_conjugate (car y))))))
;;----------------------------------------
;; One vector
(defun
 8_1 () 
 (cons (4_1)(4_0)))

;;=================
;;==Norm operation:
;; Vector Norm
(defun
 8_norm (x)
 (+ (4_norm (car x))
    (4_norm (cdr x))))

;;===================================
;;==Dot (or Inner) Product Operation:
;; Vector Dot Product
(defun
 8_dot (x y)
 (+ (4_dot (car x)(car y))
    (4_dot (cdr x)(cdr y))))

;;========================
;;==Conjugation Operation:
;; Vector conjugate
(defun
 8_conjugate (x)
 (cons (4_conjugate (car x))
  (4_- (cdr x))))

;;==========================
;; Real Vector Space Axioms:
(defthmD  
 8-Vector-closure
 (and (8p (8_0))
      (implies (and (8p x)
         (8p y))
    (8p (8_+ x y)))
      (implies (8p x)
    (8p (8_- x)))
      (implies (and (real/rationalp a)
         (8p x))
    (8p (S8_* a x)))))

(defthmD
 Associativity-of-8_+
 (implies (and (8p x)
    (8p y)
    (8p z))
     (equal (8_+ (8_+ x y) z)
      (8_+ x (8_+ y z)))))

(defthmD
 Commutativity-of-8_+
 (implies (and (8p x)
    (8p y))
     (equal (8_+ x y)
      (8_+ y x))))

(defthmD
 Unicity-of-8_0
 (implies (8p x)
     (equal (8_+ (8_0) x)
      x)))

(defthmD
 Inverse-of-8_+
 (implies (8p x)
     (equal (8_+ x (8_- x))
      (8_0))))

(defthmD
 Associativity-of-S8_*
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (8p x))
     (equal (S8_* a (S8_* b x))
      (S8_* (* a b) x))))

(defthmD
 Unicity-of-Scalar8-1
 (implies (8p x)
     (equal (S8_* 1 x) x)))

(defthmD
 Distributivity-S8_*-scalar-+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (8p x))
     (equal (S8_* (+ a b) x)
      (8_+ (S8_* a x)(S8_* b x)))))

(defthmD
 Distributivity-S8_*-8_+
 (implies (and (real/rationalp a)
    (8p x)
    (8p y))
     (equal (S8_* a (8_+ x y))
      (8_+ (S8_* a x)(S8_* a y)))))

;;=======================================
;; Additional Real Vector Algebra Axioms:
(defthmD
 8_1&8_*-closure
 (and (8p (8_1))
      (implies (and (8p x)
         (8p y))
    (8p (8_* x y)))))
;;------------------
(defthmD
 8B_*-closure
 (implies (and (8p x)
    (8p y))
     (8p (8B_* x y))))

(defthmD
 8C_*-closure
 (implies (and (8p x)
    (8p y))
     (8p (8C_* x y))))

(defthmD
 8D_*-closure
 (implies (and (8p x)
    (8p y))
     (8p (8D_* x y))))
;;----------------

(defthmD
 Not-8_1=8_0
 (not (equal (8_1)(8_0))))

(defthmD
 Left-Distributivity-8_*_8_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (8p x)
    (8p y)
    (8p z))
     (equal (8_* x 
           (8_+ (S8_* a y)
          (S8_* b z)))
      (8_+ (S8_* a
           (8_* x y))
           (S8_* b
           (8_* x z))))))
;;------------------------------
(defthmD
 Left-Distributivity-8B_*_8_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (8p x)
    (8p y)
    (8p z))
     (equal (8B_* x 
      (8_+ (S8_* a y)
           (S8_* b z)))
      (8_+ (S8_* a
           (8B_* x y))
           (S8_* b
           (8B_* x z))))))

(defthmD
 Left-Distributivity-8C_*_8_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (8p x)
    (8p y)
    (8p z))
     (equal (8C_* x 
      (8_+ (S8_* a y)
           (S8_* b z)))
      (8_+ (S8_* a
           (8C_* x y))
           (S8_* b
           (8C_* x z))))))

(defthmD
 Left-Distributivity-8D_*_8_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (8p x)
    (8p y)
    (8p z))
     (equal (8D_* x 
      (8_+ (S8_* a y)
           (S8_* b z)))
      (8_+ (S8_* a
           (8D_* x y))
           (S8_* b
           (8D_* x z))))))
;;-------------------------------

(defthmD
 Right-Distributivity-8_*_8_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (8p x)
    (8p y)
    (8p z))
     (equal (8_* (8_+ (S8_* a x)
          (S8_* b y))
           z)
      (8_+ (S8_* a
           (8_* x z))
           (S8_* b
           (8_* y z))))))
;;--------------------------
(defthmD
 Right-Distributivity-8B_*_8_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (8p x)
    (8p y)
    (8p z))
     (equal (8B_* (8_+ (S8_* a x)
           (S8_* b y))
      z)
      (8_+ (S8_* a
           (8B_* x z))
           (S8_* b
           (8B_* y z))))))

(defthmD
 Right-Distributivity-8C_*_8_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (8p x)
    (8p y)
    (8p z))
     (equal (8C_* (8_+ (S8_* a x)
           (S8_* b y))
      z)
      (8_+ (S8_* a
           (8C_* x z))
           (S8_* b
           (8C_* y z))))))

(defthmD
 Right-Distributivity-8D_*_8_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (8p x)
    (8p y)
    (8p z))
     (equal (8D_* (8_+ (S8_* a x)
           (S8_* b y))
      z)
      (8_+ (S8_* a
           (8D_* x z))
           (S8_* b
           (8D_* y z))))))
;;----------------------------

(defthmD
 Unicity-of-8_1
 (implies (8p x)
     (and (equal (8_* (8_1) x) x)
    (equal (8_* x (8_1)) x))))
;;-------------------
(defthmD
 8B_*-Unicity-of-8_1
 (implies (8p x)
     (and (equal (8B_* (8_1) x) x)
    (equal (8B_* x (8_1)) x))))

(defthmD
 8C_*-Unicity-of-8_1
 (implies (8p x)
     (and (equal (8C_* (8_1) x) x)
    (equal (8C_* x (8_1)) x))))

(defthmD
 8D_*-Unicity-of-8_1
 (implies (8p x)
     (and (equal (8D_* (8_1) x) x)
    (equal (8D_* x (8_1)) x))))
;;------------------
;;===============================================
;; Additional Vector Norm and Dot Product Axioms:
(defthmD
 Realp>=0-8_norm
 (implies (8p x)
     (and (real/rationalp (8_norm x))
    (>= (8_norm x) 0))))

(defthmD
 8_norm=0
 (implies (8p x)
     (equal (equal (8_norm x) 0)
      (equal x (8_0)))))

(defthmD   ;;Time:  22.38 seconds
 8-Composition-Law
 (implies (and (8p x)
    (8p y))
     (equal (8_norm (8_* x y))
      (* (8_norm x)
         (8_norm y)))))
;;---------------------

(defthmD   ;;Time:  22.42 seconds
 8B-Composition-Law
 (implies (and (8p x)
    (8p y))
     (equal (8_norm (8B_* x y))
      (* (8_norm x)
         (8_norm y)))))

(defthmD   ;;Time:  22.58
 8C-Composition-Law
 (implies (and (8p x)
    (8p y))
     (equal (8_norm (8C_* x y))
      (* (8_norm x)
         (8_norm y)))))

(defthmD   ;;Time:  22.35 seconds
 8D-Composition-Law
 (implies (and (8p x)
    (8p y))
     (equal (8_norm (8D_* x y))
      (* (8_norm x)
         (8_norm y)))))
;;-------------------------

(defthmD
 8_dot-def
 (equal (8_dot x y)
   (* 1/2 (+ (8_norm (8_+ x y))
       (- (8_norm x))
       (- (8_norm y)))))
 :rule-classes :definition)

(defthmD
 Distributivity-8_dot-8_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (8p x)
    (8p y)
    (8p z))
     (equal (8_dot (8_+ (S8_* a x)
            (S8_* b y))
       z)
      (+ (* a (8_dot x z))
         (* b (8_dot y z))))))

(defun-sk
 Forall-u-8_dot-u-x=0 (x)
 (forall (u)
    (implies (8p u)
       (equal (8_dot u x) 0)))
 :rewrite :direct)

(defthmD
 Forall-u-8_dot-u-x=0-def
 (equal (Forall-u-8_dot-u-x=0 x)
   (let ((u (Forall-u-8_dot-u-x=0-witness x)))
     (implies (8p u)
        (equal (8_dot u x) 0))))
 :rule-classes :definition)

;; redundant
(defthm
 Forall-u-8_dot-u-x=0-necc
 (implies (Forall-u-8_dot-u-x=0 x)
     (implies (8p u)
        (equal (8_dot u x) 0))))

(local   
(defthmD
  8_dot=0
  (implies (8p x)
      (equal (equal (8_dot x x) 0)
       (equal x (8_0))))))

(defthm  ;;8_dot is nonsingular
 Forall-u-8_dot-u-x=0->x=8_0
 (implies (and (8p x)
    (Forall-u-8_dot-u-x=0 x))
     (equal x (8_0)))
 :rule-classes nil
 :hints (("Goal"
     :in-theory (disable (:DEFINITION 8_DOT))
     :use 8_dot=0)))

(in-theory (disable Forall-u-8_dot-u-x=0-necc))

(defthmD
 8_conjugate-def-rewrite
 (implies (8p x)
     (equal (8_conjugate x)
      (8_+ (S8_* (* 2 (8_dot x (8_1)))
           (8_1))
           (8_- x)))))
;;=================================

(defthmD
 8_norm=4_norm
 (implies (4p x)
     (and (equal (8_norm (cons x (4_0)))
           (4_norm x))
    (equal (8_norm (cons (4_0) x))
           (4_norm x)))))

(defthmD  
 4p-4_0-orthogonal-4_0-4p
 (implies (and (4p x)
    (4p y))
     (equal (8_dot (cons x (4_0))
       (cons (4_0) y))
      0)))

(defthmD
 8_1-def 
 (equal (8_1)
   (cons (4_1)(4_0)))
 :rule-classes :definition)

(defthmD
 8_*-cons=cons-4_*
 (implies (and (4p x)
    (4p y))
     (equal (8_* (cons x (4_0))
           (cons y (4_0)))
      (cons (4_* x y)(4_0)))))
;;------------------------------
(defthmD
 8B_*-cons=cons-4_*
 (implies (and (4p x)
    (4p y))
     (equal (8B_* (cons x (4_0))
      (cons y (4_0)))
      (cons (4B_* x y)(4_0)))))

(defthmD
 8C_*-cons=cons-4_*
 (implies (and (4p x)
    (4p y))
     (equal (8C_* (cons x (4_0))
      (cons y (4_0)))
      (cons (4_* x y)(4_0)))))

(defthmD
 8D_*-cons=cons-4_*
 (implies (and (4p x)
    (4p y))
     (equal (8D_* (cons x (4_0))
      (cons y (4_0)))
      (cons (4B_* x y)(4_0)))))
;;-------------------------

(defthmD
 4p*i=cons-4_0-4p
 (implies (4p x)
     (equal (8_* (cons x (4_0))
           (cons (4_0)(4_1)))
      (cons (4_0) x))))
;;--------------------------
(defthmD  
 4p-8D_*-i=cons-4_0-4p
 (implies (4p x)
          (equal (8D_* (cons x (4_0))
                       (cons (4_0)(4_1)))
                 (cons (4_0) x))))
#|--------------------
(thm  
 ;;4p-8B_*-i=cons-4_0-4p
 (implies (4p x)
          (equal (8B_* (cons x (4_0))
                       (cons (4_0)(4_1)))
                 (cons (4_0) x))))
******** FAILED ********
(thm  
 ;;4p-8C_*-i=cons-4_0-4p
 (implies (4p x)
          (equal (8C_* (cons x (4_0))
                       (cons (4_0)(4_1)))
                 (cons (4_0) x))))
******** FAILED ********
-----------------------|#
(defthmD
 i-8B_*-4p=cons-4_0-4p
 (implies (4p x)
     (equal (8B_* (cons (4_0)(4_1))
      (cons x (4_0)))
      (cons (4_0) x))))
;;-----------------------
(defthmD
 i-8C_*-4p=cons-4_0-4p
 (implies (4p x)
     (equal (8C_* (cons (4_0)(4_1))
      (cons x (4_0)))
      (cons (4_0) x))))
#|-------------------------
(thm
 ;;i-8_*-4p=cons-4_0-4p
 (implies (4p x)
          (equal (8_* (cons (4_0)(4_1))
                      (cons x (4_0)))
                 (cons (4_0) x))))
******** FAILED ********
(thm
 ;;i-8D_*-4p=cons-4_0-4p
 (implies (4p x)
          (equal (8D_* (cons (4_0)(4_1))
      (cons x (4_0)))
                 (cons (4_0) x))))
******** FAILED ********
----------------------|#
;;=============================

(defun
 8_/ (x)
 (S8_* (/ (8_norm x))
  (8_conjugate x)))

(defthmD
 8p-8_/
 (implies (and (8p x)
    (not (equal x (8_0))))
     (8p (8_/ x))))

(defthmD
 8_*-8_conjugate-right
 (implies (and (real/rationalp a)
    (not (equal a 0))
    (8p x))
     (equal (8_* x (S8_* (/ a)
             (8_conjugate x)))
      (S8_* (* (/ a)
         (8_norm x))
      (8_1)))))

(defthmD
 8_*-8_conjugate-left
 (implies (and (real/rationalp a)
    (not (equal a 0))
    (8p x))
     (equal (8_* (S8_* (/ a)
           (8_conjugate x))
      x)
      (S8_* (* (/ a)
         (8_norm x))
      (8_1)))))

(defthmD
 8_/=8_*-inverse-right
 (implies (and (8p x)
    (not (equal x (8_0))))
     (equal (8_* x (8_/ x))
      (8_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION |8P|)
             (:DEFINITION 8_*)
             (:DEFINITION S8_*)
             (:DEFINITION 8_NORM)
             (:DEFINITION 8_CONJUGATE)
             (:DEFINITION |8_1|)
             (:DEFINITION |8_0|)
             (:EXECUTABLE-COUNTERPART |8_1|)
             (:EXECUTABLE-COUNTERPART |8_0|))
     :use (Realp>=0-8_norm
     8_norm=0
     (:instance
      Unicity-of-Scalar8-1
      (x (8_1)))
     (:instance
      8_*-8_conjugate-right
      (a (8_norm x)))))))

(defthmD
 8_/=8_*-inverse-left
 (implies (and (8p x)
    (not (equal x (8_0))))
     (equal (8_* (8_/ x) x)
      (8_1)))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION |8P|)
             (:DEFINITION 8_*)
             (:DEFINITION S8_*)
             (:DEFINITION 8_NORM)
             (:DEFINITION 8_CONJUGATE)
             (:DEFINITION |8_1|)
             (:DEFINITION |8_0|)
             (:EXECUTABLE-COUNTERPART |8_1|)
             (:EXECUTABLE-COUNTERPART |8_0|))
     :use (Realp>=0-8_norm
     8_norm=0
     (:instance
      Unicity-of-Scalar8-1
      (x (8_1)))
     (:instance
      8_*-8_conjugate-left
      (a (8_norm x)))))))
;;==============================
(defthmD
 8_conjugate-is-NOT-trivial
 (and (8p (cons (4_0)(4_1)))
      (not (equal (8_conjugate (cons (4_0)(4_1)))
       (identity (cons (4_0)(4_1)))))))

(defthmD
 8_*-is-NOT-commutative
 (let ((i (cons (cons (cons 0 1)(2_0))(4_0))) 
  (j (cons (cons (2_0)(2_1))(4_0)))
  (k (cons (cons (2_0)(cons 0 1))(4_0))))
   (and (8p i)
   (8p j)
   (8p k)
   (equal (8_- k)
    (cons (cons (2_0)(cons 0 -1))(4_0)))
   (not (equal (8_- k)
         k))
   (equal (8_* i j) k)
   (equal (8_* j i)(8_- k))
   (not (equal (8_* i j)
         (8_* j i))))))
;;--------------------
(defthmD
 8B_*-is-NOT-commutative
 (let ((i (cons (cons (cons 0 1)(2_0))(4_0)))
  (j (cons (cons (2_0)(2_1))(4_0)))
  (k (cons (cons (2_0)(cons 0 1))(4_0))))
   (and (8p i)
   (8p j)
   (8p k)
   (equal (8_- k)
    (cons (cons (2_0)(cons 0 -1))(4_0)))
   (not (equal (8_- k)
         k))
   (equal (8B_* i j) (8_- k))
   (equal (8B_* j i) k)
   (not (equal (8B_* i j)
         (8B_* j i))))))

(defthmD
 8C_*-is-NOT-commutative
 (let ((i (cons (cons (cons 0 1)(2_0))(4_0)))
  (j (cons (cons (2_0)(2_1))(4_0)))
  (k (cons (cons (2_0)(cons 0 1))(4_0))))
   (and (8p i)
   (8p j)
   (8p k)
   (equal (8_- k)
    (cons (cons (2_0)(cons 0 -1))(4_0)))
   (not (equal (8_- k)
         k))
   (equal (8C_* i j) k)
   (equal (8C_* j i) (8_- k))
   (not (equal (8C_* i j)
         (8C_* j i))))))

(defthmD
 8D_*-is-NOT-commutative
 (let ((i (cons (cons (cons 0 1)(2_0))(4_0)))
  (j (cons (cons (2_0)(2_1))(4_0)))
  (k (cons (cons (2_0)(cons 0 1))(4_0))))
   (and (8p i)
   (8p j)
   (8p k)
   (equal (8_- k)
    (cons (cons (2_0)(cons 0 -1))(4_0)))
   (not (equal (8_- k)
         k))
   (equal (8D_* i j)(8_- k))
   (equal (8D_* j i) k) 
   (not (equal (8D_* i j)
         (8D_* j i))))))
;;---------------

(defthmD
 8_*-is-NOT-associative
 (let ((e5 (cons (4_0)(4_1)))
  (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
  (e7 (cons (4_0)(cons (2_0)(2_1))))
  (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
   (and (8p e5)
   (8p e6)
   (8p e7)
   (8p e8)
   (equal (8_- e8)
    (cons (4_0)(cons (2_0)(cons 0 -1))))
   (not (equal (8_- e8)
         e8))
   (equal (8_* (8_* e5 e6) e7)
    (8_- e8))
   (equal (8_* e5 (8_* e6 e7))
    e8)
   (not (equal (8_* (8_* e5 e6) e7)
         (8_* e5 (8_* e6 e7)))))))
;;------------------------
(defthmD
 8B_*-is-NOT-associative
 (let ((e5 (cons (4_0)(4_1)))
  (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
  (e7 (cons (4_0)(cons (2_0)(2_1))))
  (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
   (and (8p e5)
   (8p e6)
   (8p e7)
   (8p e8)
   (equal (8_- e8)
    (cons (4_0)(cons (2_0)(cons 0 -1))))
   (not (equal (8_- e8)
         e8))
   (equal (8B_* (8B_* e5 e6) e7)
    (8_- e8))
   (equal (8B_* e5 (8B_* e6 e7))
    e8)
   (not (equal (8B_* (8B_* e5 e6) e7)
         (8B_* e5 (8B_* e6 e7)))))))

(defthmD
 8C_*-is-NOT-associative
 (let ((e5 (cons (4_0)(4_1)))
  (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
  (e7 (cons (4_0)(cons (2_0)(2_1))))
  (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
   (and (8p e5)
   (8p e6)
   (8p e7)
   (8p e8)
   (equal (8_- e8)
    (cons (4_0)(cons (2_0)(cons 0 -1))))
   (not (equal (8_- e8)
         e8))
   (equal (8C_* (8C_* e5 e6) e7)
    e8)
   (equal (8C_* e5 (8C_* e6 e7))
    (8_- e8))
   (not (equal (8C_* (8C_* e5 e6) e7)
         (8C_* e5 (8C_* e6 e7)))))))

(defthmD
 8D_*-is-NOT-associative
 (let ((e5 (cons (4_0)(4_1)))
  (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
  (e7 (cons (4_0)(cons (2_0)(2_1))))
  (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
   (and (8p e5)
   (8p e6)
   (8p e7)
   (8p e8)
   (equal (8_- e8)
    (cons (4_0)(cons (2_0)(cons 0 -1))))
   (not (equal (8_- e8)
         e8))
   (equal (8D_* (8D_* e5 e6) e7)
    e8)
   (equal (8D_* e5 (8D_* e6 e7))
    (8_- e8))
   (not (equal (8D_* (8D_* e5 e6) e7)
         (8D_* e5 (8D_* e6 e7)))))))
;;-------------------------
(defthmD
 Not-8_*=8B_*
 (let ((e5 (cons (4_0)(4_1)))
  (e6 (cons (4_0)(cons (cons 0 1)(2_0)))))
   (not (equal (8_*  e5 e6)
    (8B_* e5 e6)))))

(defthmD
 Not-8_*=8C_*
 (let ((e5 (cons (4_0)(4_1)))
  (e6 (cons (4_0)(cons (cons 0 1)(2_0)))))
   (not (equal (8_*  e5 e6)
    (8C_* e5 e6)))))

(defthmD
 Not-8_*=8D_*
 (let ((e6 (cons (4_0)(cons (cons 0 1)(2_0))))
  (e7 (cons (4_0)(cons (2_0)(2_1)))))
   (not (equal (8_*  e6 e7)
    (8D_* e6 e7)))))

(defthmD
 Not-8B_*=8C_*
 (let ((e6 (cons (4_0)(cons (cons 0 1)(2_0))))
  (e7 (cons (4_0)(cons (2_0)(2_1)))))
   (not (equal (8B_* e6 e7)
    (8C_* e6 e7)))))

(defthmD
 Not-8B_*=8D_*
 (let ((e5 (cons (4_0)(4_1)))
  (e6 (cons (4_0)(cons (cons 0 1)(2_0)))))
   (not (equal (8B_* e5 e6)
    (8D_* e5 e6)))))

(defthmD
 Not-8C_*=8D_*
 (let ((e5 (cons (4_0)(4_1)))
  (e6 (cons (4_0)(cons (cons 0 1)(2_0)))))
   (not (equal (8C_* e5 e6)
    (8D_* e5 e6)))))
;;------------------

(defthmD
 8_*=8B_*-reverse
 (implies (and (8p x)
    (8p y))
     (equal (8_*  x y)
      (8B_* y x))))

(defthmD
 8C_*=8D_*-reverse
 (implies (and (8p x)
    (8p y))
     (equal (8C_* x y)
      (8D_* y x))))
#|============================================
 Recall the definition of 8_*:
(defun
 8_* (x y)
 (cons (4_+ (4_* (car x)
      (car y))
       (4_- (4_* (4_conjugate (cdr y))
           (cdr x))))
  (4_+ (4_* (cdr y) 
      (car x))
       (4_* (cdr x)
      (4_conjugate (car y))))))
============================|#
;; Since 4_* is NOT commutative,
;;   changing the order of some of the products
;;   would change the multiplication:
(defun
 8A_* (x y)
 (cons (4_+ (4_* (car x)
      (car y))
       (4_- (4_* (cdr x)
           (4_conjugate (cdr y)))))
  (4_+ (4_* (car x)
      (cdr y)) 
       (4_* (cdr x)
      (4_conjugate (car y))))))
;; Using the original definition of 8_*:
;;  The product of nonzero values is always nonzero.
;; With the alternative definition of 8A_*.
;;  the product of nonzero values could be zero.
(defthmD
 8A_*-zero-divisors
 (let ((x (cons (cons (cons 0 -1)(2_0))(cons (2_0)(2_1))))
  (y (cons (cons (cons 0  1)(2_0))(cons (2_0)(2_1)))))
   (and (8p x)
   (8p y)
   (equal (8_* x y)(cons (4_0)(cons (2_0)(cons 0 2))))
   (equal (8A_* x y)(8_0))
   (not (equal (8_* x y)
         (8A_* x y))))))
;;===============================================
;; 8_conjugate is an isomorphism from 8p with 8_*
;;  onto 8p with 8B_*.

;; Also
;; 8_conjugate is an isomorphism from 8p with 8C_*
;;  onto 8p with 8D_*.

(defthmD
 8p-8_conjugate
 (implies (8p x)
     (8p (8_conjugate x))))

(defthm
 8_conjugate-is-1to1
 (implies (and (8p x)
    (8p y)
    (equal (8_conjugate x)
           (8_conjugate y)))
     (equal x y))
 :rule-classes nil)

(defthmD
 8_conjugate-is-onto
 (implies (8p x)
     (and (8p (8_conjugate x))
    (equal (8_conjugate (8_conjugate x))
           x))))

(defthmD
 8_conjugate-8_0
 (equal (8_conjugate (8_0))
   (8_0)))

(defthmD
 8_conjugate-8_1
 (equal (8_conjugate (8_1))
   (8_1)))

(defthmD
 8_conjugate-8_+
 (implies (and (8p x)
    (8p y))
     (equal (8_conjugate (8_+ x y))
      (8_+ (8_conjugate x)
           (8_conjugate y)))))

(defthmD
 8_conjugate-8_*
 (implies (and (8p x)
    (8p y))
     (equal (8_conjugate (8_* x y))
      (8B_* (8_conjugate x)
      (8_conjugate y)))))

(defthmD
 8_conjugate-8C_*
 (implies (and (8p x)
    (8p y))
     (equal (8_conjugate (8C_* x y))
      (8D_* (8_conjugate x)
      (8_conjugate y)))))

(defthmD
 8_conjugate-S8_*
 (implies (and (real/rationalp a)
    (8p x))
     (equal (8_conjugate (S8_* a x))
      (S8_* a (8_conjugate x)))))

(defthmD
 8_conjugate-8_-
 (implies (8p x)
     (equal (8_conjugate (8_- x))
      (8_- (8_conjugate x)))))

(defthmD
 8_conjugate-8_/
 (implies (and (8p x)
    (not (equal x (8_0))))
     (equal (8_conjugate (8_/ x))
      (8_/ (8_conjugate x)))))
;;======================================
;;==Real Vector Space Operations:
;; Predicate for set of vectors
(defun
 7p (x)
 (and (consp x)
      (3p (car x))
      (4p (cdr x))))

;; Zero vector
(defun
 7_0 () 
 (cons (3_0)(4_0)))

;; Vector addition
(defun
 7_+ (x y) 
 (cons (3_+ (car x)(car y))
  (4_+ (cdr x)(cdr y))))

;; Vector minus
(defun
 7_- (x)
 (cons (3_- (car x))
  (4_- (cdr x))))

;; Scalar multiplication
(defun
 S7_* (a x)
 (cons (S3_* a (car x))
  (S4_* a (cdr x))))

;; Vector Norm
(defun
 7_norm (x)
 (+ (3_norm (car x))
    (4_norm (cdr x))))

;; Vector Dot Product
(defun
 7_dot (x y)
 (+ (3_dot (car x)(car y))
    (4_dot (cdr x)(cdr y))))
;;==========================
;; Real Vector Space Axioms:
(defthmD  
 7-Vector-closure
 (and (7p (7_0))
      (implies (and (7p x)
         (7p y))
    (7p (7_+ x y)))
      (implies (7p x)
    (7p (7_- x)))
      (implies (and (real/rationalp a)
         (7p x))
    (7p (S7_* a x)))))

(defthmD
 Associativity-of-7_+
 (implies (and (7p x)
    (7p y)
    (7p z))
     (equal (7_+ (7_+ x y) z)
      (7_+ x (7_+ y z)))))

(defthmD
 Commutativity-of-7_+
 (implies (and (7p x)
    (7p y))
     (equal (7_+ x y)
      (7_+ y x))))

(defthmD
 Unicity-of-7_0
 (implies (7p x)
     (equal (7_+ (7_0) x)
      x)))

(defthmD
 Inverse-of-7_+
 (implies (7p x)
     (equal (7_+ x (7_- x))
      (7_0))))

(defthmD
 Associativity-of-S7_*
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (7p x))
     (equal (S7_* a (S7_* b x))
      (S7_* (* a b) x))))

(defthmD
 Unicity-of-Scalar7-1
 (implies (7p x)
     (equal (S7_* 1 x) x)))

(defthmD
 Distributivity-S7_*-scalar-+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (7p x))
     (equal (S7_* (+ a b) x)
      (7_+ (S7_* a x)(S7_* b x)))))

(defthmD
 Distributivity-S7_*-7_+
 (implies (and (real/rationalp a)
    (7p x)
    (7p y))
     (equal (S7_* a (7_+ x y))
      (7_+ (S7_* a x)(S7_* a y)))))
;;=============================
(defun
 8_RealPart (x)
 (caaar x))

(defun
 8_VectorPart (x)
 (cons (cons (cdaar x)
        (cdar x))
  (cdr x)))

(defthmD
 Closure-8_Real&8_Vector-Part
 (implies (8p x)
     (and (real/rationalp (8_RealPart x))
    (7p (8_VectorPart x)))))

(defun
 Real&7p-to-8p (a x)
 (cons (cons (cons a (caar x))
        (cdar x))
  (cdr x)))

(defthmD
 8p-Real&7p-to-8p
 (implies (and (real/rationalp a)
    (7p x))
     (8p (Real&7p-to-8p a x))))

(defun
 7p-to-8p (x)
 (cons (cons (cons 0 (caar x))
        (cdar x))
  (cdr x)))

(defthmD
 8p-7p-to-8p
 (implies (7p x)
     (8p (7p-to-8p x))))
;;===================
;; 7D Vector Cross Product
(defun     
 7_X (x y)
 (8_VectorPart (S8_* 1/2 (8_+ (8_* (7p-to-8p x)
            (7p-to-8p y))
             (8_- (8_* (7p-to-8p y)
           (7p-to-8p x)))))))

(defthmD
 8_RealPart-of-8p-7_X-def
 (implies (and (7p x)
    (7p y))
     (equal (8_RealPart (S8_* 1/2 (8_+ (8_* (7p-to-8p x)
              (7p-to-8p y))
               (8_- (8_* (7p-to-8p y)
                   (7p-to-8p x))))))
      0)))
;;===============================================
;; Additional Vector norm, Vector Cross and Dot Product Axioms:
(defthmD
 Realp>=0-7_norm
 (implies (7p x)
     (and (real/rationalp (7_norm x))
    (>= (7_norm x) 0))))

(defthmD
 7_norm=0
 (implies (7p x)
     (equal (equal (7_norm x) 0)
      (equal x (7_0)))))

(defthmD  
 7_dot&3_X-closure
 (implies (and (7p x)
    (7p y))
     (and (real/rationalp (7_dot x y))
    (7p (7_X x y)))))

(defthmD
 Distributivity-7_dot-7_+
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (7p x)
    (7p y)
    (7p z))
     (equal (7_dot (7_+ (S7_* a x)
            (S7_* b y))
       z)
      (+ (* a (7_dot x z))
         (* b (7_dot y z))))))

(defun-sk
 Forall-u-7_dot-u-x=0 (x)
 (forall (u)
    (implies (7p u)
       (equal (7_dot u x) 0)))
 :rewrite :direct)

(defthmD
 Forall-u-7_dot-u-x=0-def
 (equal (Forall-u-7_dot-u-x=0 x)
   (let ((u (Forall-u-7_dot-u-x=0-witness x)))
     (implies (7p u)
        (equal (7_dot u x) 0))))
 :rule-classes :definition)

;; redundant
(defthm
 Forall-u-7_dot-u-x=0-necc
 (implies (Forall-u-7_dot-u-x=0 x)
     (implies (7p u)
        (equal (7_dot u x) 0))))

(local   
(defthmD
  7_dot=0
  (implies (7p x)
      (equal (equal (7_dot x x) 0)
       (equal x (7_0))))))

(defthm  ;;7_dot is nonsingular
 Forall-u-7_dot-u-x=0->x=7_0
 (implies (and (7p x)
    (Forall-u-7_dot-u-x=0 x))
     (equal x (7_0)))
 :rule-classes nil
 :hints (("Goal"
     :in-theory (disable (:DEFINITION 7_DOT))
     :use 7_dot=0)))

(in-theory (disable Forall-u-7_dot-u-x=0-necc))

(defthm
 7_X-orthagonal-x&y
 (implies (and (7p x)
    (7p y))
     (and (equal (7_dot x (7_X x y)) 0)
    (equal (7_dot y (7_X x y)) 0))))

(defthmD
 7_X-is-NOT-commutative
 (let ((i (cons (cons 1 (2_0))
     (4_0)))
  (j (cons (cons 0 (2_1))
     (4_0))))
   (and (7p i)
   (7p j)
   (not (equal (7_X i j)
         (7_X j i))))))

(defthmD
 7_X-is-NOT-associative
 (let ((i (cons (cons 1 (2_0))
     (4_0)))
  (j (cons (cons 0 (2_1))
     (4_0))))
   (and (7p i)
   (7p j)
   (not (equal (7_X (7_X i i) j)
         (7_X i (7_X i j)))))))

(defthm
 7_X-is-nilpotent
 (implies (7p x)
     (equal (7_X x x)(7_0))))

(defthmD
 7_X-nullity-of-7_0
 (implies (7p x)
     (and (equal (7_X (7_0) x)(7_0))
    (equal (7_X x (7_0))(7_0)))))

(defthmD
 7_X-is-anticommutative
 (implies (and (7p x)
    (7p y))
     (and (equal (7_- (7_X x y))
           (7_X y x))
    (equal (7_X (7_- x) y)
           (7_X y x))
    (equal (7_X x (7_- y))
           (7_X y x)))))

(defthmD
 Distributivity-7_X-7_+-right
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (7p x)
    (7p y)
    (7p z))
     (equal (7_X (7_+ (S7_* a x)
          (S7_* b y))
           z)
      (7_+ (S7_* a (7_X x z))
           (S7_* b (7_X y z))))))

(defthmD
 Distributivity-7_X-7_+-left
 (implies (and (real/rationalp a)
    (real/rationalp b)
    (7p x)
    (7p y)
    (7p z))
     (equal (7_X x
           (7_+ (S7_* a y)
          (S7_* b z)))
      (7_+ (S7_* a (7_X x y))
           (S7_* b (7_X x z))))))

(defthmD
 8_norm-Real&7p-to-8p=1_norm+7_norm
 (implies (and (real/rationalp a)
    (7p x))
     (equal (8_norm (Real&7p-to-8p a x))
      (+ (1_norm a)
         (7_norm x)))))

(defthmD    ;;Time:  4.46 seconds
 8_norm-8_*-7p-to-8p=7_norm*7_norm
 (implies (and (7p x)
    (7p y))
     (equal (8_norm (8_* (7p-to-8p x)
             (7p-to-8p y)))
      (* (7_norm x)
         (7_norm y)))))

(defthmD
 8_*=7_dot-7_X
 (implies (and (7p x)
    (7p y))
     (equal (8_* (7p-to-8p x)
           (7p-to-8p y))
      (Real&7p-to-8p (- (7_dot x y))
         (7_X x y)))))

(defthmD
 1_norm-7_dot+7_norm-7_X
 (implies (and (7p x)
    (7p y))
     (equal (+ (1_norm (7_dot x y))
         (7_norm (7_X x y)))
      (* (7_norm x)
         (7_norm y))))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION |7P|)
             (:DEFINITION 7P-TO-8P)
             (:DEFINITION 7_DOT)
             (:DEFINITION 7_norm)
             (:DEFINITION 8_norm)
             (:DEFINITION |7_X|)
             (:DEFINITION 8_*)
             (:DEFINITION REAL&7P-TO-8P))
     :use ((:instance
      8_norm-Real&7p-to-8p=1_norm+7_norm
      (a (- (7_dot x y)))
      (x (7_X x y)))
     8_norm-8_*-7p-to-8p=7_norm*7_norm
     8_*=7_dot-7_X))))

(defthmD
 7_dot=8_RealPart-8_*
 (implies (and (7p x)
    (7p y))
     (equal (7_dot x y)
      (8_RealPart (S8_* -1/2 (8_+ (8_* (7p-to-8p x)
               (7p-to-8p y))
                (8_* (7p-to-8p y)
               (7p-to-8p x))))))))

(defthm
 7_Grassman-identity-FAILS
 (let ((i (cons (cons 1 (2_0))
     (4_0)))
  (j (cons (cons 0 (2_1))
     (4_0)))
  (k (cons (cons 0 (cons 0 1))
     (4_0)))
  (p (cons (cons 0 (2_0))
     (4_1))))
   (and (7p i)
   (7p j)
   (7p k)
   (7p p)
   (equal (7_X p (7_X i j))
    (7_X p k))
   (equal (7_+ (S7_* (7_dot p j) i)
         (7_- (S7_* (7_dot p i) j)))
    (7_0))
   (not (equal (7_X p (7_X i j))
         (7_+ (S7_* (7_dot p j) i)
        (7_- (S7_* (7_dot p i) j))))))))

(defthmD
 7_Jacobi-identity-FAILS
 (let ((i (cons (cons 1 (2_0))
     (4_0)))
  (j (cons (cons 0 (2_1))
     (4_0)))
  (k (cons (cons 0 (cons 0 1))
     (4_0)))
  (p (cons (cons 0 (2_0))
     (4_1))))
   (and (7p i)
   (7p j)
   (7p k)
   (7p p)
   (equal (7_+ (7_X p (7_X i j))
         (7_+ (7_X i (7_X j p))
        (7_X j (7_X p i))))
    (S7_* 3 (7_X p k)))
   (not (equal (7_+ (7_X p (7_X i j))
        (7_+ (7_X i (7_X j p))
             (7_X j (7_X p i))))
         (7_0))))))

(defthmD
 7_dot-7_X=8_dot-8_*
 (implies (and (7p x)
    (7p y)
    (7p z))
     (equal (7_dot (7_X x y)
       z)
      (8_dot (8_* (7p-to-8p x)
            (7p-to-8p y))
       (7p-to-8p z)))))

(defthmD
 7_Interchange-rule
 (implies (and (7p x)
    (7p y)
    (7p z))
     (equal (7_dot (7_X x y)
       z)
      (7_dot x 
       (7_X y z)))))

(defthmD
 7_norm-7_X=1
 (implies (and (7p x)
    (7p y)
    (equal (7_norm x) 1)
    (equal (7_norm y) 1)
    (equal (7_dot x y) 0))
     (equal (7_norm (7_X x y)) 1))
 :hints (("Goal"
     :in-theory (disable (:DEFINITION 7_DOT)
             (:DEFINITION 7_NORM)
             (:DEFINITION |7_X|))
    :use 1_norm-7_dot+7_norm-7_X)))

(defthmD
 7_X-x-7_X-x-y
 (implies (and (7p x)
    (7p y))
     (equal (7_X x
           (7_X x y))
      (7_+ (S7_* (7_dot x y) x)
           (7_- (S7_* (7_norm x) y))))))

#|==============================
(thm
(let ((e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
  (and (equal (8_* e2 e2)(8A_* e2 e2))
  (equal (8_* e2 e3)(8A_* e2 e3))
  (equal (8_* e2 e4)(8A_* e2 e4))
  (equal (8_* e2 e5)(8A_* e2 e5))
  (equal (8_* e2 e6)(8A_* e2 e6))
       (equal (8_* e2 e7)(8_- (8A_* e2 e7)))    ;;==     
  (equal (8_* e2 e8)(8_- (8A_* e2 e8)))))) ;;==

(thm
(let ((e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
  (and (equal (8_* e3 e2)(8A_* e3 e2))
  (equal (8_* e3 e3)(8A_* e3 e3))      
  (equal (8_* e3 e4)(8A_* e3 e4))
  (equal (8_* e3 e5)(8A_* e3 e5))
  (equal (8_* e3 e6)(8_- (8A_* e3 e6)))    ;;== 
       (equal (8_* e3 e7)(8A_* e3 e7))        
  (equal (8_* e3 e8)(8_- (8A_* e3 e8)))))) ;;==

(thm
(let ((e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
  (and (equal (8_* e4 e2)(8A_* e4 e2))
  (equal (8_* e4 e3)(8A_* e4 e3))      
  (equal (8_* e4 e4)(8A_* e4 e4)) 
  (equal (8_* e4 e5)(8A_* e4 e5))
  (equal (8_* e4 e6)(8_- (8A_* e4 e6))) ;;==       
       (equal (8_* e4 e7)(8_- (8A_* e4 e7))) ;;==
  (equal (8_* e4 e8)(8A_* e4 e8)))))

(thm
(let ((e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
  (and (equal (8_* e5 e2)(8A_* e5 e2))
  (equal (8_* e5 e3)(8A_* e5 e3))      
  (equal (8_* e5 e4)(8A_* e5 e4)) 
  (equal (8_* e5 e5)(8A_* e5 e5))
  (equal (8_* e5 e6)(8A_* e5 e6))       
  (equal (8_* e5 e7)(8A_* e5 e7))
  (equal (8_* e5 e8)(8A_* e5 e8)))))

(thm
(let ((e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
  (and (equal (8_* e6 e2)(8A_* e6 e2))
  (equal (8_* e6 e3)(8A_* e6 e3))
  (equal (8_* e6 e4)(8A_* e6 e4)) 
  (equal (8_* e6 e5)(8A_* e6 e5))
  (equal (8_* e6 e6)(8A_* e6 e6))         
  (equal (8_* e6 e7)(8_- (8A_* e6 e7)))     ;;==
  (equal (8_* e6 e8)(8_- (8A_* e6 e8))))))  ;;==

(thm
(let ((e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
  (and (equal (8_* e7 e2)(8A_* e7 e2))
  (equal (8_* e7 e3)(8A_* e7 e3))
  (equal (8_* e7 e4)(8A_* e7 e4))
  (equal (8_* e7 e5)(8A_* e7 e5))
      (equal (8_* e7 e6)(8_- (8A_* e7 e6)))     ;;==
  (equal (8_* e7 e7)(8A_* e7 e7))
  (equal (8_* e7 e8)(8_- (8A_* e7 e8))))))  ;;==

(thm
(let ((e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
  (and (equal (8_* e8 e2)(8A_* e8 e2))
  (equal (8_* e8 e3)(8A_* e8 e3))
  (equal (8_* e8 e4)(8A_* e8 e4))
  (equal (8_* e8 e5)(8A_* e8 e5))
      (equal (8_* e8 e6)(8_- (8A_* e8 e6)))  ;;==
  (equal (8_* e8 e7)(8_- (8A_* e8 e7)))  ;;==
  (equal (8_* e8 e8)(8A_* e8 e8)))))
======================|#
#|====================
(let ((e1 (cons (4_1)(4_0)))
     (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
     (e3 (cons (cons (2_0)(2_1))(4_0)))
     (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
     (e5 (cons (4_0)(4_1)))
     (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
     (e7 (cons (4_0)(cons (2_0)(2_1))))
     (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (list e1 e2 e3 e4 e5 e6 e7 e8))
((((1 . 0) 0 . 0) (0 . 0) 0 . 0)
(((0 . 1) 0 . 0) (0 . 0) 0 . 0)
(((0 . 0) 1 . 0) (0 . 0) 0 . 0)
(((0 . 0) 0 . 1) (0 . 0) 0 . 0)
(((0 . 0) 0 . 0) (1 . 0) 0 . 0)
(((0 . 0) 0 . 0) (0 . 1) 0 . 0)
(((0 . 0) 0 . 0) (0 . 0) 1 . 0)
(((0 . 0) 0 . 0) (0 . 0) 0 . 1))

(let ((e1 (cons (4_1)(4_0)))
     (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
     (e3 (cons (cons (2_0)(2_1))(4_0)))
     (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
     (e5 (cons (4_0)(4_1)))
     (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
     (e7 (cons (4_0)(cons (2_0)(2_1))))
     (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (list (8_* e1 e1)
  (8_* e1 e2)
  (8_* e1 e3)
  (8_* e1 e4)
  (8_* e1 e5)
  (8_* e1 e6)
  (8_* e1 e7)
  (8_* e1 e8)))
((((1 . 0) 0 . 0) (0 . 0) 0 . 0)
(((0 . 1) 0 . 0) (0 . 0) 0 . 0)
(((0 . 0) 1 . 0) (0 . 0) 0 . 0)
(((0 . 0) 0 . 1) (0 . 0) 0 . 0)
(((0 . 0) 0 . 0) (1 . 0) 0 . 0)
(((0 . 0) 0 . 0) (0 . 1) 0 . 0)
(((0 . 0) 0 . 0) (0 . 0) 1 . 0)
(((0 . 0) 0 . 0) (0 . 0) 0 . 1))

(thm
(let ((e1 (cons (4_1)(4_0)))
      (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (and (equal (8_* e1 e1) e1)
      (equal (8_* e1 e2) e2)
      (equal (8_* e1 e3) e3)
      (equal (8_* e1 e4) e4)
      (equal (8_* e1 e5) e5)
      (equal (8_* e1 e6) e6)
      (equal (8_* e1 e7) e7)
      (equal (8_* e1 e8) e8))))

(let ((e1 (cons (4_1)(4_0)))
     (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
     (e3 (cons (cons (2_0)(2_1))(4_0)))
     (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
     (e5 (cons (4_0)(4_1)))
     (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
     (e7 (cons (4_0)(cons (2_0)(2_1))))
     (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (list (8_* e2 e1)
  (8_* e2 e2)
  (8_* e2 e3)
  (8_* e2 e4)
  (8_* e2 e5)
  (8_* e2 e6)
  (8_* e2 e7)
  (8_* e2 e8)))
((((0 . 1) 0 . 0) (0 . 0) 0 . 0)
(((-1 . 0) 0 . 0) (0 . 0) 0 . 0)
(((0 . 0) 0 . 1) (0 . 0) 0 . 0)
(((0 . 0) -1 . 0) (0 . 0) 0 . 0)
(((0 . 0) 0 . 0) (0 . 1) 0 . 0)
(((0 . 0) 0 . 0) (-1 . 0) 0 . 0)
(((0 . 0) 0 . 0) (0 . 0) 0 . -1)
(((0 . 0) 0 . 0) (0 . 0) 1 . 0))

(thm
(let ((e1 (cons (4_1)(4_0)))
      (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (and (equal (8_* e2 e1) e2)
      (equal (8_* e2 e2)(8_- e1))
      (equal (8_* e2 e3) e4)
      (equal (8_* e2 e4)(8_- e3))
      (equal (8_* e2 e5) e6)
      (equal (8_* e2 e6)(8_- e5))
      (equal (8_* e2 e7)(8_- e8))
      (equal (8_* e2 e8) e7))))

(let ((e1 (cons (4_1)(4_0)))
     (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
     (e3 (cons (cons (2_0)(2_1))(4_0)))
     (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
     (e5 (cons (4_0)(4_1)))
     (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
     (e7 (cons (4_0)(cons (2_0)(2_1))))
     (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (list (8_* e3 e1)
  (8_* e3 e2)
  (8_* e3 e3)
  (8_* e3 e4)
  (8_* e3 e5)
  (8_* e3 e6)
  (8_* e3 e7)
  (8_* e3 e8)))
((((0 . 0) 1 . 0) (0 . 0) 0 . 0)
(((0 . 0) 0 . -1) (0 . 0) 0 . 0)
(((-1 . 0) 0 . 0) (0 . 0) 0 . 0)
(((0 . 1) 0 . 0) (0 . 0) 0 . 0)
(((0 . 0) 0 . 0) (0 . 0) 1 . 0)
(((0 . 0) 0 . 0) (0 . 0) 0 . 1)
(((0 . 0) 0 . 0) (-1 . 0) 0 . 0)
(((0 . 0) 0 . 0) (0 . -1) 0 . 0))

(thm
(let ((e1 (cons (4_1)(4_0)))
      (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (and (equal (8_* e3 e1) e3)
      (equal (8_* e3 e2)(8_- e4))
      (equal (8_* e3 e3)(8_- e1))
      (equal (8_* e3 e4) e2)
      (equal (8_* e3 e5) e7)
      (equal (8_* e3 e6) e8)
      (equal (8_* e3 e7)(8_- e5))
      (equal (8_* e3 e8)(8_- e6)))))

(let ((e1 (cons (4_1)(4_0)))
     (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
     (e3 (cons (cons (2_0)(2_1))(4_0)))
     (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
     (e5 (cons (4_0)(4_1)))
     (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
     (e7 (cons (4_0)(cons (2_0)(2_1))))
     (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (list (8_* e4 e1)
  (8_* e4 e2)
  (8_* e4 e3)
  (8_* e4 e4)
  (8_* e4 e5)
  (8_* e4 e6)
  (8_* e4 e7)
  (8_* e4 e8)))
((((0 . 0) 0 . 1) (0 . 0) 0 . 0)
(((0 . 0) 1 . 0) (0 . 0) 0 . 0)
(((0 . -1) 0 . 0) (0 . 0) 0 . 0)
(((-1 . 0) 0 . 0) (0 . 0) 0 . 0)
(((0 . 0) 0 . 0) (0 . 0) 0 . 1)
(((0 . 0) 0 . 0) (0 . 0) -1 . 0)
(((0 . 0) 0 . 0) (0 . 1) 0 . 0)
(((0 . 0) 0 . 0) (-1 . 0) 0 . 0))

(thm
(let ((e1 (cons (4_1)(4_0)))
      (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (and (equal (8_* e4 e1) e4)
      (equal (8_* e4 e2) e3)
      (equal (8_* e4 e3)(8_- e2))
      (equal (8_* e4 e4)(8_- e1))
      (equal (8_* e4 e5) e8)
      (equal (8_* e4 e6)(8_- e7))
      (equal (8_* e4 e7) e6)
      (equal (8_* e4 e8)(8_- e5)))))

(let ((e1 (cons (4_1)(4_0)))
     (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
     (e3 (cons (cons (2_0)(2_1))(4_0)))
     (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
     (e5 (cons (4_0)(4_1)))
     (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
     (e7 (cons (4_0)(cons (2_0)(2_1))))
     (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (list (8_* e5 e1)
  (8_* e5 e2)
  (8_* e5 e3)
  (8_* e5 e4)
  (8_* e5 e5)
  (8_* e5 e6)
  (8_* e5 e7)
  (8_* e5 e8)))
((((0 . 0) 0 . 0) (1 . 0) 0 . 0)
(((0 . 0) 0 . 0) (0 . -1) 0 . 0)
(((0 . 0) 0 . 0) (0 . 0) -1 . 0)
(((0 . 0) 0 . 0) (0 . 0) 0 . -1)
(((-1 . 0) 0 . 0) (0 . 0) 0 . 0)
(((0 . 1) 0 . 0) (0 . 0) 0 . 0)
(((0 . 0) 1 . 0) (0 . 0) 0 . 0)
(((0 . 0) 0 . 1) (0 . 0) 0 . 0))

(thm
(let ((e1 (cons (4_1)(4_0)))
      (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (and (equal (8_* e5 e1) e5)
      (equal (8_* e5 e2)(8_- e6))
      (equal (8_* e5 e3)(8_- e7))
      (equal (8_* e5 e4)(8_- e8))
      (equal (8_* e5 e5)(8_- e1))
      (equal (8_* e5 e6) e2)
      (equal (8_* e5 e7) e3)
      (equal (8_* e5 e8) e4))))

(let ((e1 (cons (4_1)(4_0)))
     (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
     (e3 (cons (cons (2_0)(2_1))(4_0)))
     (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
     (e5 (cons (4_0)(4_1)))
     (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
     (e7 (cons (4_0)(cons (2_0)(2_1))))
     (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (list (8_* e6 e1)
  (8_* e6 e2)
  (8_* e6 e3)
  (8_* e6 e4)
  (8_* e6 e5)
  (8_* e6 e6)
  (8_* e6 e7)
  (8_* e6 e8)))
((((0 . 0) 0 . 0) (0 . 1) 0 . 0)
(((0 . 0) 0 . 0) (1 . 0) 0 . 0)
(((0 . 0) 0 . 0) (0 . 0) 0 . -1)
(((0 . 0) 0 . 0) (0 . 0) 1 . 0)
(((0 . -1) 0 . 0) (0 . 0) 0 . 0)
(((-1 . 0) 0 . 0) (0 . 0) 0 . 0)
(((0 . 0) 0 . -1) (0 . 0) 0 . 0)
(((0 . 0) 1 . 0) (0 . 0) 0 . 0))

(thm
(let ((e1 (cons (4_1)(4_0)))
      (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (and (equal (8_* e6 e1) e6)
      (equal (8_* e6 e2) e5)
      (equal (8_* e6 e3)(8_- e8))
      (equal (8_* e6 e4) e7)
      (equal (8_* e6 e5)(8_- e2))
      (equal (8_* e6 e6)(8_- e1))
      (equal (8_* e6 e7)(8_- e4))
      (equal (8_* e6 e8) e3))))

(let ((e1 (cons (4_1)(4_0)))
     (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
     (e3 (cons (cons (2_0)(2_1))(4_0)))
     (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
     (e5 (cons (4_0)(4_1)))
     (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
     (e7 (cons (4_0)(cons (2_0)(2_1))))
     (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (list (8_* e7 e1)
  (8_* e7 e2)
  (8_* e7 e3)
  (8_* e7 e4)
  (8_* e7 e5)
  (8_* e7 e6)
  (8_* e7 e7)
  (8_* e7 e8)))
((((0 . 0) 0 . 0) (0 . 0) 1 . 0)
(((0 . 0) 0 . 0) (0 . 0) 0 . 1)
(((0 . 0) 0 . 0) (1 . 0) 0 . 0)
(((0 . 0) 0 . 0) (0 . -1) 0 . 0)
(((0 . 0) -1 . 0) (0 . 0) 0 . 0)
(((0 . 0) 0 . 1) (0 . 0) 0 . 0)
(((-1 . 0) 0 . 0) (0 . 0) 0 . 0)
(((0 . -1) 0 . 0) (0 . 0) 0 . 0))

(thm
(let ((e1 (cons (4_1)(4_0)))
      (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (and (equal (8_* e7 e1) e7)
      (equal (8_* e7 e2) e8)
      (equal (8_* e7 e3) e5)
      (equal (8_* e7 e4)(8_- e6))
      (equal (8_* e7 e5)(8_- e3))
      (equal (8_* e7 e6) e4)
      (equal (8_* e7 e7)(8_- e1))
      (equal (8_* e7 e8)(8_- e2)))))

(let ((e1 (cons (4_1)(4_0)))
     (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
     (e3 (cons (cons (2_0)(2_1))(4_0)))
     (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
     (e5 (cons (4_0)(4_1)))
     (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
     (e7 (cons (4_0)(cons (2_0)(2_1))))
     (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (list (8_* e8 e1)
  (8_* e8 e2)
  (8_* e8 e3)
  (8_* e8 e4)
  (8_* e8 e5)
  (8_* e8 e6)
  (8_* e8 e7)
  (8_* e8 e8)))
((((0 . 0) 0 . 0) (0 . 0) 0 . 1)
(((0 . 0) 0 . 0) (0 . 0) -1 . 0)
(((0 . 0) 0 . 0) (0 . 1) 0 . 0)
(((0 . 0) 0 . 0) (1 . 0) 0 . 0)
(((0 . 0) 0 . -1) (0 . 0) 0 . 0)
(((0 . 0) -1 . 0) (0 . 0) 0 . 0)
(((0 . 1) 0 . 0) (0 . 0) 0 . 0)
(((-1 . 0) 0 . 0) (0 . 0) 0 . 0))

(thm
(let ((e1 (cons (4_1)(4_0)))
      (e2 (cons (cons (cons 0 1)(2_0))(4_0)))
      (e3 (cons (cons (2_0)(2_1))(4_0)))
      (e4 (cons (cons (2_0)(cons 0 1))(4_0)))
      (e5 (cons (4_0)(4_1)))
      (e6 (cons (4_0)(cons (cons 0 1)(2_0))))
      (e7 (cons (4_0)(cons (2_0)(2_1))))
      (e8 (cons (4_0)(cons (2_0)(cons 0 1)))))
 (and (equal (8_* e8 e1) e8)
      (equal (8_* e8 e2)(8_- e7))
      (equal (8_* e8 e3) e6)
      (equal (8_* e8 e4) e5)
      (equal (8_* e8 e5)(8_- e4))
      (equal (8_* e8 e6)(8_- e3))
      (equal (8_* e8 e7) e2)
      (equal (8_* e8 e8)(8_- e1)))))
==============|#
#|===============================
   e1  e2  e3  e4  e5  e6  e7  e8
---------------------------------
e1| e1  e2  e3  e4  e5  e6  e7  e8
e2| e2 -e1  e4 -e3  e6 -e5 -e8  e7
e3| e3 -e4 -e1  e2  e7  e8 -e5 -e6
e4| e4  e3 -e2 -e1  e8 -e7  e6 -e5
e5| e5 -e6 -e7 -e8 -e1  e2  e3  e4
e6| e6  e5 -e8  e7 -e2 -e1 -e4  e3
e7| e7  e8  e5 -e6 -e3  e4 -e1 -e2
e8| e8 -e7  e6  e5 -e4 -e3  e2 -e1

    1   I   J   K   L  IL  JL  KL
---------------------------------
1|  1   I   J   K   L  1L  JL  KL
I|  I  -1   K  -J  IL  -L -KL  JL
J|  J  -K  -1   I  JL  KL  -L -IL
K|  K   J  -I  -1  KL -JL  IL  -L
L|  L -IL -JL -KL  -1   I   J   K
IL| IL   L -KL  JL  -I  -1  -K   J
JL| JL  KL   L -IL  -J   K  -1  -I
KL| KL -JL  IL   L  -K  -J   I  -1
=============================|#