;;======polylist.lisp============ 
;; ACL2 & ACL2(r) book for 
;; Polynomials, of one variable, with acl2-numberp coefficients, 
;; implemented with lists of acl2-numbers. 

;; (a_0 a_1 a_2 ... a_n) represents the polynomial 
;; a_0 + a_1*x + a_2*x^2 + ... + a_n*x^n 

;; ---------------- 
;; Any list of only zeros, including the empty list, 
;; represents the ZERO POLYNOMIAL. 

;; A CONSTANT POLYNOMIAL is either the empty list 
;; or a list constructed by (CONS numberp zero-poly) 

;; A DENSE HORNER NORMAL FORM (DHNF) is an acl2-number-listp, 
;; either NIL or (a_0 a_1 a_2 ... a_n), with a_n not equal 0. 

;; ----------------- 
;; (EVAL-POLYNOMIAL poly z) computes the output value of poly 
;; for input value z. 

;; An acl2-numberp, z, is a ZERO OF A POLYNOMIAL, poly, 
;; just in case (eval-polynomial poly z) = 0. 
;; That is, z is a root of the equation, poly = 0. 

;; REV is reverse for lists. 
;; For a nonzero acl2-numberp z, 
;; (/ z) is a zero of (rev poly) 
;; iff 
;; z is a zero of poly. 

;; ---------------- 
;; If poly1 & poly2 represent polynomials p1(x) & p2(x), 
;; then (COMPOSE-POLYNOMIALS poly1 poly2) represnts 
;; the polynomial p1(p2(x)). 

;; If poly represents polynomial p(x), then 
;; (COMPOSE-POLY-WITH_-X poly), defined by 
;; (compose-polynomials poly (list 0 -1)), 
;; represents the polynomial p(-x). 
;; For an acl2-numberp, z, 
;; (- z) is a zero of (compose-poly-with_-x poly) 
;; iff 
;; z is a zero of poly. 

;; If poly represents polynomial p(x), then 
;; (COMPOSE-POLY-WITH_X^2 poly), defined by 
;; (compose-polynomials poly (list 0 0 1)), 
;; represents the polynomial p(x^2). 

;; For ACL2 & ACL2(r): 
;; For an acl2-numberp, z, 
;; z is a zero of (compose-poly-with_x^2 poly) 
;; iff 
;; z^2 is a zero of poly. 

;; For ACL2(r): 
;; For a nonnegative realp, z, 
;; (acl2-sqrt z) is a zero of (compose-poly-with_x^2 poly) 
;; iff 
;; z is a zero of poly. 

;; For ACL2(r): 
;; For a negative realp, z, 
;; (acl2-sqrt -z)i is a zero of (compose-poly-with_x^2 poly) 
;; iff 
;; z is a zero of poly. 

;; If poly represents polynomial p(x), then 
;; (COMPOSE-POLY-WITH_X+D poly d), defined by 
;; (compose-polynomials poly (list d 1)), 
;; represents the polynomial p(x+d). 
;; For an acl2-numberp, z, 
;; (- z d) is a zero of (compose-poly-with_x+d poly d) 
;; iff 
;; z is a zero of poly. 

;; -------------- 
;; For a nonzero poly, 
;; (find-distinct-zeros-of-poly poly) 
;; is a [noncomputable] list, 
;; without duplicates, 
;; of all the acl2-numberp zeros of poly. 
;; 
;; (len (find-distinct-zeros-of-poly poly)) < (len poly) 

;; -------------- 
;; Using evaluation to prove equality of polynomials. 

;; Two theorems proved in this book: 

;; FORALL-X-EVAL-POLY=EVAL-POLY_=_EQUAL 
;; (implies (and (dhnf-p poly1) 
;; (dhnf-p poly2)) 
;; (equal (forall x (equal (eval-polynomial poly1 x) 
;; (eval-polynomial poly2 x))) 
;; (equal poly1) 
;; poly2)) 
;; 

;; FORALL-X-EVAL-POLY=EVAL-POLY_=_EQUAL-TRUNCATE-POLY 
;; (implies (and (polynomial-p poly1) 
;; (polynomial-p poly2)) 
;; (equal (forall x (equal (eval-polynomial poly1 x) 
;; (eval-polynomial poly2 x))) 
;; (equal (truncate-polynomial poly1) 
;; (truncate-polynomial poly2)))) 

;; ==================== 
;; Polynomial Functions 
;; polynomial-p 
;; zero-polynomial-p [Recognizes (any representation of) the ZERO poly] 
;; constant-polynomial-p 
;; eval-polynomial 
;; leading-coeff 
;; eval-poly-with-expt 
;; polynomial-zero-p [Recognizes any zero of poly] 
;; polynomial-- 
;; scale-polynomial 
;; polynomial-+ 
;; polynomial-* 
;; add-const-polynomial 
;; compose-polynomials 
;; compose-poly-with_-x 
;; compose-poly-with_x^2 
;; compose-poly-with_x+d 
;; alt-minus [alt-minus=compose-poly-with_-x] 
;; append-leading-zero 
;; shift-polynomial [shift-polynomial=compose-poly-with_x+d] 
;; divide-polynomial-with-remainder-by-x+a 
;; nonconstant-polynomial-zero-p [Recognizes any zero of nonconstant poly] 
;; divide-polynomial-by-list 
;; distinct-nonconstant-polynomial-zero-list-p 
;; choose-new-zero 
;; exists-another-zero 
;; exists-another-zero-witness 
;; choose-n-distinct-zeros 
;; find-distinct-zeros-of-poly 
;; truncate-polynomial 
;; dhnf-p 
;; DHscale-polynomial 
;; DHpolynomial-+ 
;; DHpolynomial-* 
;; DHcompose-polynomials 
;; max-norm-1C-list 
;; next-integer 
;; not-list-equiv-witness 
;; dhnf-p-list-equiv-witness 
;; forall-x-eval-poly=eval-poly 
;; forall-x-eval-poly=eval-poly-witness 

;; 15 FEB 2019 

(in-package "ACL2") 

#|============================ 
To certify: 
(certify-book "polylist" 
0 ;; world with no commands 
) 
=============================== 
To use: 
(include-book "polylist" 
:uncertified-okp nil 
:defaxioms-okp nil 
:skip-proofs-okp nil 
) 
================================ 
(LD "polylist.lisp") ; read and evaluate each form in file 
=============================== 
:set-gag-mode t ; enable gag-mode, suppressing most proof commentary 
(set-gag-mode t) ; same as above 
:set-gag-mode :goals ; same as above, but print names of goals when produced 
:set-gag-mode nil ; disable gag-mode 
================================ 
ACL2 Version 8.1 built February 11, 2019 15:37:06. 
System books directory "/home/acl2/acl2-8.1/acl2-8.1/books/". 
------------------------------------------------------------- 
ACL2 Version 8.1(r) built September 21, 2018 08:17:49. 
System books directory "/home/acl2/acl2-8.1r/acl2-8.1/books/". 
=================================|# 
(local 
 (include-book "arithmetic/top-with-meta" 
               :dir :system 
               :uncertified-okp nil 
               :defaxioms-okp nil 
               :skip-proofs-okp nil)) 

;; Includes defun for REV[reverse for lists] 
(include-book "std/lists/top" 
              :dir :system 
              :uncertified-okp nil 
              :defaxioms-okp nil 
              :skip-proofs-okp nil) 

(local 
 (include-book "std/lists/butlast" 
               :dir :system 
               :uncertified-okp nil 
               :defaxioms-okp nil 
               :skip-proofs-okp nil)) 

;; includes ACL2(r) defun for acl2-sqrt 
#+:non-standard-analysis 
(include-book "nonstd/nsa/sqrt" 
              :dir :system 
              :uncertified-okp nil 
              :defaxioms-okp nil 
              :skip-proofs-okp nil) 

(include-book "norm-1C" 
              :uncertified-okp nil 
              :defaxioms-okp nil 
              :skip-proofs-okp nil) 

#-:non-standard-analysis 
(include-book "floor1-non-R" 
              :uncertified-okp nil 
              :defaxioms-okp nil 
              :skip-proofs-okp nil) 

(defun 
    polynomial-p (poly) 
  (declare (xargs :guard t)) 
  (if (consp poly) 
      (and (acl2-numberp (car poly)) 
           (polynomial-p (cdr poly))) 
    (null poly))) 

(defthm 
  polynomial-p-forward-to-acl2-number-listp 
  (implies (polynomial-p poly) 
           (acl2-number-listp poly)) 
  :rule-classes :forward-chaining) 

(defun 
    zero-polynomial-p (poly) 
  (declare (xargs :guard t)) 
  (if (consp poly) 
      (and (equal (car poly) 0) 
           (zero-polynomial-p (cdr poly))) 
    (null poly))) 

(defthm 
  zero-polynomial-p-forward-to-polynomial-p 
  (implies (zero-polynomial-p poly) 
           (polynomial-p poly)) 
  :rule-classes :forward-chaining) 

(defun 
    constant-polynomial-p (poly) 
  (declare (xargs :guard t)) 
  (if (consp poly) 
      (and (acl2-numberp (car poly)) 
           (zero-polynomial-p (cdr poly))) 
    (null poly))) 

#|================== 
(defthmD 
zero-polynomial-p-forward-to-constant-polynomial-p 
(implies (zero-polynomial-p poly) 
(constant-polynomial-p poly)) 
:rule-classes :forward-chaining) 
================|# 
#|============== 
(defthmD 
constant-polynomial-p-forward-to-polynomial-p 
(implies (constant-polynomial-p poly) 
(polynomial-p poly)) 
:rule-classes :forward-chaining) 
==============|# 

(defthm 
  not-constant-polynomial-has-len-2+ 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly))) 
           (< 1 (len poly)))) 

;; Horner Rule Evaluation 
(defun 
    eval-polynomial (poly x) 
  (if (consp poly) 
      (+ (car poly) 
         (* x (eval-polynomial (cdr poly) x))) 
    0)) 

(defthm 
  eval-zero-polynomial-p 
  (implies (zero-polynomial-p poly) 
           (equal (eval-polynomial poly z) 0))) 

(defthm 
  eval-constant-polynomial-p 
  (implies (and (constant-polynomial-p poly) 
                (consp (double-rewrite poly))) 
           (equal (eval-polynomial poly z) 
                  (car (double-rewrite poly))))) 

(defun 
    leading-coeff (poly) 
  (first (last poly))) 

(defthm 
  polynomial-p-all-but-last 
  (implies (polynomial-p poly) 
           (polynomial-p (all-but-last poly)))) 
;; Using the book, "std/lists/top", 
;; in the system directory, ACL2 proves 

;; (thm 
;; (equal (all-but-last lst) 
;; (take (+ -1 (len lst)) lst))) 
;;------------- 
;; Using the book, "std/lists/butlast", 
;; in the system directory, ACL2 proves 

;; (thm 
;; (equal (all-but-last lst) 
;; (butlast lst 1))) 
;;------------- 
;; Without any books, ACL2 proves 

;; (thm 
;; (equal (butlast lst 1) 
;; (take (+ -1 (len lst)) lst))) 
;;=============== 

(defthm 
  len-all-but-last 
  (implies (consp (double-rewrite lst)) 
           (equal (len (all-but-last lst)) 
                  (1- (len (double-rewrite lst)))))) 

(defun 
    eval-poly-with-expt (poly z) 
  (if (consp poly) 
      (+ (* (leading-coeff poly) 
            (expt z (1- (len poly)))) 
         (eval-poly-with-expt (all-but-last poly) z)) 
    0)) 

(defthmD 
  split-eval-polynomial 
  (equal (+ (eval-polynomial (all-but-last poly) z) 
            (* (car (last poly)) 
               (expt z (+ -1 (len poly))))) 
         (eval-polynomial poly z))) 

(defthm 
  eval-poly-with-expt-is-eval-poly 
  (equal (eval-poly-with-expt poly z) 
         (eval-polynomial poly z)) 
  :hints (("Goal" 
           :in-theory (enable split-eval-polynomial)))) 

(defthm 
  polynomial-p-rev 
  (implies (polynomial-p poly) 
           (polynomial-p (rev poly)))) 

(defthm 
  integer-listp-rev 
  (implies (integer-listp poly) 
           (integer-listp (rev poly)))) 

(defthm 
  rational-listp-rev 
  (implies (rational-listp poly) 
           (rational-listp (rev poly)))) 

#+:non-standard-analysis 
(defthm 
  real-listp-rev 
  (implies (real-listp poly) 
           (real-listp (rev poly)))) 

(defthm 
  acl2-number-listp-rev 
  (implies (acl2-number-listp poly) 
           (acl2-number-listp (rev poly)))) 

(defthmD 
  split-eval-polynomial-rev 
  (equal (+ (eval-polynomial (all-but-last (rev poly)) z) 
            (* (car poly) 
               (expt z (+ -1 (len poly))))) 
         (eval-polynomial (rev poly) z)) 
  :hints (("Goal" 
           :use (:instance 
                 split-eval-polynomial 
                 (poly (rev poly)))))) 

(defthmD 
  all-but-last=take 
  (equal (all-but-last lst) 
         (take (+ -1 (len (double-rewrite lst))) 
               (double-rewrite lst)))) 

(defthmD 
  take-rev=rev-cdr 
  (equal (take (+ -1 (len lst))(rev lst)) 
         (rev (cdr lst)))) 

(defthm 
  all-but-last-rev=rev-cdr 
  (equal (all-but-last (rev lst)) 
         (rev (cdr lst))) 
  :hints (("Goal" 
           :in-theory (enable all-but-last=take 
                              take-rev=rev-cdr)))) 

(defthmD 
  eval-polynomial-rev-1/2 
  (IMPLIES (AND (CONSP (double-rewrite POLY)) 
                (ACL2-NUMBERP (CAR (double-rewrite POLY))) 
                (EQUAL (EVAL-POLYNOMIAL (REV (CDR POLY)) z) 
                       (* (EVAL-POLYNOMIAL (CDR POLY) (/ z)) 
                          (EXPT z (+ -1 (LEN (CDR (double-rewrite POLY))))))) 
                (POLYNOMIAL-P (CDR POLY)) 
                (ACL2-NUMBERP z) 
                (NOT (EQUAL 0 z))) 
           (EQUAL (EVAL-POLYNOMIAL (REV POLY) z) 
                  (+ (* (CAR (double-rewrite POLY)) 
                        (EXPT z (+ -1 (LEN (double-rewrite POLY))))) 
                     (* (/ z) 
                        (EVAL-POLYNOMIAL (CDR POLY) (/ z)) 
                        (EXPT z (+ -1 (LEN (double-rewrite POLY)))))))) 
  :hints (("Goal" 
           :use split-eval-polynomial-rev))) 

(defthm 
  eval-polynomial-rev 
  (implies (and (polynomial-p poly) 
                (acl2-numberp z) 
                (not (equal 0 z))) 
           (equal (eval-polynomial (rev poly) z) 
                  (* (eval-polynomial poly (/ z)) 
                     (expt z (+ -1 (len (double-rewrite poly))))))) 
  :hints (("Goal" 
           :in-theory (enable eval-polynomial-rev-1/2)))) 

(defthm 
  eval-polynomial-rev-recip=0 
  (implies (and (polynomial-p poly) 
                (acl2-numberp z) 
                (not (equal z 0))) 
           (equal (equal (eval-polynomial (rev poly)(/ z)) 0) 
                  (equal (eval-polynomial poly z) 0)))) 

;; z is a zero of poly 
;; That is, z is a root of the equation: poly=0 
(defun 
    polynomial-zero-p (poly z) 
  (and (acl2-numberp z) 
       (equal (eval-polynomial poly z) 0))) 

(defthm 
  polynomial-zero-p-rev-recip=polynomial-zero-p 
  (implies (and (polynomial-p poly) 
                (acl2-numberp z) 
                (not (equal z 0))) 
           (equal (polynomial-zero-p (rev poly)(/ z)) 
                  (polynomial-zero-p poly z)))) 

(defun 
    polynomial-- (poly) 
  (if (consp poly) 
      (cons (- (car poly)) 
            (polynomial-- (cdr poly))) 
    nil)) 

(defthm 
  polynomial-p-polynomial-- 
  (polynomial-p (polynomial-- poly))) 

(defthm 
  integer-listp-polynomial-- 
  (implies (integer-listp poly) 
           (integer-listp (polynomial-- poly)))) 

(defthm 
  rational-listp-polynomial-- 
  (implies (rational-listp poly) 
           (rational-listp (polynomial-- poly)))) 

#+:non-standard-analysis 
(defthm 
  real-listp-polynomial-- 
  (implies (real-listp poly) 
           (real-listp (polynomial-- poly)))) 

(defthm 
  eval-polynomial-polynomial-- 
  (equal (eval-polynomial (polynomial-- poly) z) 
         (- (eval-polynomial poly z)))) 

(defthm 
  consp-polynomial-- 
  (equal (consp (polynomial-- lst)) 
         (consp (double-rewrite lst)))) 

(defthm 
  len-polynomial-- 
  (equal (len (polynomial-- poly)) 
         (len (double-rewrite poly)))) 

(defthm 
  car-last-polynomial-- 
  (implies (consp (double-rewrite poly)) 
           (equal (car (last (polynomial-- poly))) 
                  (- (car (last (double-rewrite poly))))))) 

(defun 
    scale-polynomial (poly c) 
  (if (consp poly) 
      (cons (* c (car poly)) 
            (scale-polynomial (cdr poly) c)) 
    nil)) 

(defthm 
  polynomial-p-scale-polynomial 
  (polynomial-p (scale-polynomial poly c))) 

(defthm 
  integer-listp-scale-polynomial 
  (implies (and (integer-listp poly) 
                (integerp c)) 
           (integer-listp (scale-polynomial poly c)))) 

(defthm 
  rational-listp-scale-polynomial 
  (implies (and (rational-listp poly) 
                (rationalp c)) 
           (rational-listp (scale-polynomial poly c)))) 

#+:non-standard-analysis 
(defthm 
  real-listp-scale-polynomial 
  (implies (and (real-listp poly) 
                (realp c)) 
           (real-listp (scale-polynomial poly c)))) 

(defthm 
  eval-polynomial-scale-polynomial 
  (equal (eval-polynomial (scale-polynomial poly c) x) 
         (* c (eval-polynomial poly x)))) 

(defthm 
  len-scale-polynomial 
  (equal (len (scale-polynomial poly k)) 
         (len (double-rewrite poly)))) 

(defthm 
  car-last-scale-polynomial 
  (implies (consp (double-rewrite poly)) 
           (equal (car (last (scale-polynomial poly c))) 
                  (* c (car (last (double-rewrite poly))))))) 

(defun 
    polynomial-+ (poly1 poly2) 
  (if (consp poly1) 
      (if (consp poly2) 
          (cons (+ (car poly1) 
                   (car poly2)) 
                (polynomial-+ (cdr poly1)(cdr poly2))) 
        poly1) 
    poly2)) 

(defthm 
  polynomial-p-polynomial-+ 
  (implies (and (polynomial-p poly1) 
                (polynomial-p poly2)) 
           (polynomial-p (polynomial-+ poly1 poly2)))) 

(defthm 
  integer-listp-polynomial-+ 
  (implies (and (integer-listp poly1) 
                (integer-listp poly2)) 
           (integer-listp (polynomial-+ poly1 poly2)))) 

(defthm 
  rational-listp-polynomial-+ 
  (implies (and (rational-listp poly1) 
                (rational-listp poly2)) 
           (rational-listp (polynomial-+ poly1 poly2)))) 

#+:non-standard-analysis 
(defthm 
  real-listp-polynomial-+ 
  (implies (and (real-listp poly1) 
                (real-listp poly2)) 
           (real-listp (polynomial-+ poly1 poly2)))) 

(defthm 
  acl2-number-listp-polynomial-+ 
  (implies (and (acl2-number-listp poly1) 
                (acl2-number-listp poly2)) 
           (acl2-number-listp (polynomial-+ poly1 poly2)))) 

(defthm 
  consp-polynomial-+ 
  (equal (consp (polynomial-+ poly1 poly2)) 
         (or (consp (double-rewrite poly1)) 
             (consp (double-rewrite poly2))))) 

(defthm 
  eval-polynomial-polynomial-+ 
  (equal (eval-polynomial (polynomial-+ poly1 poly2) x) 
         (+ (eval-polynomial poly1 x) 
            (eval-polynomial poly2 x)))) 

(defthm 
  len-polynomial-+ 
  (equal (len (polynomial-+ poly1 poly2)) 
         (max (len (double-rewrite poly1)) 
              (len (double-rewrite poly2))))) 

(defthmD 
  associativity-of-polynomial-+ 
  (equal (polynomial-+ (polynomial-+ poly1 poly2) 
                       poly3) 
         (polynomial-+ poly1 
                       (polynomial-+ poly2 poly3)))) 

(defthmD 
  commutativity-of-polynomial-+ 
  (implies (and (polynomial-p poly1) 
                (polynomial-p poly2)) 
           (equal (polynomial-+ poly1 poly2) 
                  (polynomial-+ poly2 poly1)))) 

(defthmD 
  commutativity-2-of-polynomial-+ 
  (implies (and (polynomial-p poly1) 
                (polynomial-p poly2)) 
           (equal (polynomial-+ poly1 
                                (polynomial-+ poly2 poly3)) 
                  (polynomial-+ poly2 
                                (polynomial-+ poly1 poly3))))) 

(defthm 
  car-last-polynomial-+-A 
  (implies (and (consp (double-rewrite poly1)) 
                (equal (len (double-rewrite poly1))(len (double-rewrite poly2)))) 
           (equal (car (last (polynomial-+ poly1 poly2))) 
                  (+ (car (last (double-rewrite poly1))) 
                     (car (last (double-rewrite poly2))))))) 

(defthm 
  car-last-polynomial-+-B 
  (implies (and (consp (double-rewrite poly2)) 
                (equal (len (double-rewrite poly1))(len (double-rewrite poly2)))) 
           (equal (car (last (polynomial-+ poly1 poly2))) 
                  (+ (car (last (double-rewrite poly1))) 
                     (car (last (double-rewrite poly2))))))) 

(defthm 
  car-last-polynomial-+-C 
  (implies (< (len (double-rewrite poly1))(len (double-rewrite poly2))) 
           (equal (car (last (polynomial-+ poly1 poly2))) 
                  (car (last (double-rewrite poly2)))))) 

(defthm 
  car-last-polynomial-+-D 
  (implies (< (len (double-rewrite poly2))(len (double-rewrite poly1))) 
           (equal (car (last (polynomial-+ poly1 poly2))) 
                  (car (last (double-rewrite poly1)))))) 

(defun 
    polynomial-* (poly1 poly2) 
  (if (consp poly1) 
      (polynomial-+ (scale-polynomial poly2 (car poly1)) 
                    (cons 0 (polynomial-* (cdr poly1) poly2))) 
    nil)) 

(defthm 
  polynomial-p-polynomial-* 
  (polynomial-p (polynomial-* poly1 poly2))) 

(defthm 
  integer-listp-polynomial-* 
  (implies (and (integer-listp poly1) 
                (integer-listp poly2)) 
           (integer-listp (polynomial-* poly1 poly2)))) 

(defthm 
  rational-listp-polynomial-* 
  (implies (and (rational-listp poly1) 
                (rational-listp poly2)) 
           (rational-listp (polynomial-* poly1 poly2)))) 

#+:non-standard-analysis 
(defthm 
  real-listp-polynomial-* 
  (implies (and (real-listp poly1) 
                (real-listp poly2)) 
           (real-listp (polynomial-* poly1 poly2)))) 

(defthm 
  consp-polynomial-* 
  (equal (consp (polynomial-* poly1 poly2)) 
         (consp (double-rewrite poly1)))) 
;; (polynomial-* '(1 2) nil) => (0 0) 
;; (polynomial-* nil '(1 2)) => NIL 
;;============ 

(defthm 
  eval-polynomial-polynomial-* 
  (equal (eval-polynomial (polynomial-* poly1 poly2) x) 
         (* (eval-polynomial poly1 x) 
            (eval-polynomial poly2 x)))) 

(defthm 
  len-polynomial-* 
  (equal (len (polynomial-* poly1 poly2)) 
         (cond ((atom (double-rewrite poly1)) 
                0) 
               ((atom (double-rewrite poly2)) 
                (len (double-rewrite poly1))) 
               (t (+ -1 
                     (len (double-rewrite poly1)) 
                     (len (double-rewrite poly2))))))) 

(defthm 
  polynomial-+_poly_zero=poly 
  (implies (and (polynomial-p poly) 
                (consp (double-rewrite poly))) 
           (equal (polynomial-+ poly (list 0)) 
                  poly))) 

(defthm 
  car-last-polynomial-* 
  (implies (and (consp (double-rewrite poly1)) 
                (polynomial-p poly1) 
                (consp (double-rewrite poly2)) 
                (polynomial-p poly2)) 
           (equal (car (last (polynomial-* poly1 poly2))) 
                  (* (car (last (double-rewrite poly1))) 
                     (car (last (double-rewrite poly2))))))) 

(defthm 
  acl2-numberp-car-last 
  (implies (and (consp lst) 
                (acl2-number-listp lst)) 
           (acl2-numberp (car (last lst)))) 
  :rule-classes :type-prescription) 

(defthm 
  NOT-car-last-polynomial-*=0 
  (implies (and (consp (double-rewrite poly1)) 
                (polynomial-p poly1) 
                (not (equal (car (last (double-rewrite poly1))) 0)) 
                (consp (double-rewrite poly2)) 
                (polynomial-p poly2) 
                (not (equal (car (last (double-rewrite poly2))) 0))) 
           (not (equal (car (last (polynomial-* poly1 poly2))) 0)))) 

(defun 
    add-const-polynomial (poly k) 
  (if (consp poly) 
      (cons (+ k (car poly)) 
            (cdr poly)) 
    (list k))) 

(defthmD 
  polynomial-p-add-const-polynomial 
  (implies (and (polynomial-p poly) 
                (acl2-numberp k)) 
           (polynomial-p (add-const-polynomial poly k)))) 

(defthmD 
  eval-polynomial-add-const-polynomial 
  (equal (eval-polynomial (add-const-polynomial poly k) z) 
         (+ k (eval-polynomial poly z)))) 

(defthmD 
  len-add-const-polynomial 
  (equal (len (add-const-polynomial lst k)) 
         (if (consp (double-rewrite lst)) 
             (len (double-rewrite lst)) 
           1))) 

(defthmD 
  car-last-add-const-polynomial 
  (equal (car (last (add-const-polynomial poly k))) 
         (cond ((atom (double-rewrite poly)) k) 
               ((atom (cdr (double-rewrite poly)))(+ k (car (double-rewrite poly)))) 
               (t (car (last (double-rewrite poly))))))) 

(defthmD 
  integer-listp-add-const-polynomial 
  (implies (and (integer-listp poly) 
                (integerp k)) 
           (integer-listp (add-const-polynomial poly k)))) 

(defthmD 
  rational-listp-add-const-polynomial 
  (implies (and (rational-listp poly) 
                (rationalp k)) 
           (rational-listp (add-const-polynomial poly k)))) 

#+:non-standard-analysis 
(defthmD 
  real-listp-add-const-polynomial 
  (implies (and (real-listp poly) 
                (realp k)) 
           (real-listp (add-const-polynomial poly k)))) 

(defthmD 
  acl2-number-listp-add-const-polynomial 
  (implies (and (acl2-number-listp poly) 
                (acl2-numberp k)) 
           (acl2-number-listp (add-const-polynomial poly k)))) 

(defun 
    compose-polynomials (poly1 poly2) 
  (cond ((atom poly1) 
         poly1) 
        ((atom (cdr poly1)) 
         poly1) 
        (t (add-const-polynomial (polynomial-* poly2 
                                               (compose-polynomials (cdr poly1) poly2)) 
                                 (car poly1))))) 

(defthmD 
  polynomial-p-compose-polynomials-lemma 
  (polynomial-p (cdr (polynomial-* poly2 
                                   (compose-polynomials (cdr poly1) poly2))))) 

(defthm 
  polynomial-p-compose-polynomials 
  (implies (polynomial-p poly1) 
           (polynomial-p (compose-polynomials poly1 poly2))) 
  :hints (("Goal" 
           :in-theory (enable polynomial-p-compose-polynomials-lemma)))) 

(defthm 
  integer-listp-compose-polynomials 
  (implies (and (integer-listp poly1) 
                (integer-listp poly2)) 
           (integer-listp (compose-polynomials poly1 poly2))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION ADD-CONST-POLYNOMIAL))))) 

(defthm 
  rational-listp-compose-polynomials 
  (implies (and (rational-listp poly1) 
                (rational-listp poly2)) 
           (rational-listp (compose-polynomials poly1 poly2))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION ADD-CONST-POLYNOMIAL))))) 

#+:non-standard-analysis 
(defthm 
  real-listp-compose-polynomials 
  (implies (and (real-listp poly1) 
                (real-listp poly2)) 
           (real-listp (compose-polynomials poly1 poly2))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION ADD-CONST-POLYNOMIAL))))) 

(defthm 
  acl2-number-listp-compose-polynomials 
  (implies (acl2-number-listp poly1) 
           (acl2-number-listp (compose-polynomials poly1 poly2))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION ADD-CONST-POLYNOMIAL))))) 

(defthm 
  eval-polynomial-compose-polynomials 
  (equal (eval-polynomial (compose-polynomials poly1 poly2) z) 
         (eval-polynomial poly1 (eval-polynomial poly2 z))) 
  :hints (("Goal" 
           :in-theory (e/d (eval-polynomial-add-const-polynomial) 
                           ((:DEFINITION ADD-CONST-POLYNOMIAL)))))) 

(defthm 
  consp-compose-polynomials 
  (equal (consp (compose-polynomials poly1 poly2)) 
         (consp (double-rewrite poly1)))) 

(defthm 
  len-compose-polynomials 
  (equal (len (compose-polynomials poly1 poly2)) 
         (cond ((atom (double-rewrite poly1)) 0) 
               ((atom (double-rewrite poly2)) 1) 
               ((atom (cdr (double-rewrite poly1))) 1) 
               (t (+ 2 
                     (- (len (double-rewrite poly1))) 
                     (- (len (double-rewrite poly2))) 
                     (* (len (double-rewrite poly1)) 
                        (len (double-rewrite poly2))))))) 
  :hints (("Goal" 
           :in-theory (e/d (len-add-const-polynomial) 
                           ((:DEFINITION ADD-CONST-POLYNOMIAL)))))) 

(defthm 
  not-consp-cdr-compose-polynomials 
  (implies (and (consp (cdr (double-rewrite poly1))) 
                (atom (cdr (double-rewrite poly2)))) 
           (not (consp (cdr (compose-polynomials poly1 poly2)))))) 

(defthm 
  last-compose-polynomials 
  (implies (and (consp (cdr (double-rewrite poly1))) 
                (atom (cdr (double-rewrite poly2)))) 
           (equal (last (compose-polynomials poly1 poly2)) 
                  (compose-polynomials poly1 poly2))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION COMPOSE-POLYNOMIALS))))) 

(defthm 
  eval-constant-polynomial-p-1 
  (implies (and (polynomial-p poly) 
                (consp (double-rewrite poly)) 
                (atom (cdr (double-rewrite poly)))) 
           (equal (eval-polynomial poly z) 
                  (car (double-rewrite poly))))) 

(defthm 
  eval-poly-compose-polys=car-compose-polys 
  (implies (and (polynomial-p poly1) 
                (consp (cdr (double-rewrite poly1))) 
                (atom (cdr (double-rewrite poly2)))) 
           (equal (eval-polynomial (compose-polynomials poly1 poly2) z) 
                  (car (compose-polynomials poly1 poly2)))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION COMPOSE-POLYNOMIALS) 
                               EVAL-POLYNOMIAL-COMPOSE-POLYNOMIALS)))) 

(defthm 
  car-last-compose-polys=eval-poly 
  (implies (and (polynomial-p poly1) 
                (consp (cdr (double-rewrite poly1))) 
                (atom (cdr (double-rewrite poly2)))) 
           (equal (car (last (compose-polynomials poly1 poly2))) 
                  (eval-polynomial poly1 (car (double-rewrite poly2))))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION COMPOSE-POLYNOMIALS) 
                               eval-poly-compose-polys=car-compose-polys) 
           :use eval-poly-compose-polys=car-compose-polys))) 

(defthm 
  car-last-compose-polys=car 
  (implies (and (consp (double-rewrite poly1)) 
                (atom (double-rewrite poly2))) 
           (equal (car (last (compose-polynomials poly1 poly2))) 
                  (car (double-rewrite poly1))))) 

(defthm 
  car-last-compose-polys=car-a 
  (implies (and (consp (double-rewrite poly1)) 
                (consp (double-rewrite poly2)) 
                (atom (cdr (double-rewrite poly1)))) 
           (equal (car (last (compose-polynomials poly1 poly2))) 
                  (car (double-rewrite poly1))))) 

(defthm 
  car-last-compose-polys=nil 
  (implies (atom (double-rewrite poly1)) 
           (equal (car (last (compose-polynomials poly1 poly2))) 
                  nil))) 

#|============== 
(defthm 
consp-cdr-polynomial-*-poly-cdr 
(implies (consp (cdr (double-rewrite poly2))) 
(consp (cdr (polynomial-* poly2 (cdr poly1)))))) 
===============|# 

(defthm 
  consp-cdr-polynomial-*-poly-compose-polys 
  (implies (consp (cdr (double-rewrite poly2))) 
           (consp (cdr (polynomial-* poly2 
                                     (compose-polynomials (cdr poly1) 
                                                          poly2)))))) 

;; ACL2 Warning [Double-rewrite] 
(defthmD 
  car-last-compose-polys=expt-a 
  (implies (and (polynomial-p poly1) 
                (polynomial-p poly2) 
                (consp (cdr (double-rewrite poly1))) 
                (consp (cdr (double-rewrite poly2)))) 
           (equal (car (last (compose-polynomials poly1 poly2))) 
                  (* (car (last (double-rewrite poly1))) 
                     (expt (car (last (double-rewrite poly2))) 
                           (+ -1 (len poly1)))))) 
  :hints (("Goal" 
           :in-theory (e/d (car-last-add-const-polynomial) 
                           ((:DEFINITION ADD-CONST-POLYNOMIAL) 
                            (:DEFINITION POLYNOMIAL-*)))))) 

(defthm 
  car-last-compose-polys=expt 
  (implies (and (polynomial-p poly1) 
                (polynomial-p poly2) 
                (consp (cdr (double-rewrite poly1))) 
                (consp (cdr (double-rewrite poly2)))) 
           (equal (car (last (compose-polynomials poly1 poly2))) 
                  (* (car (last (double-rewrite poly1))) 
                     (expt (car (last (double-rewrite poly2))) 
                           (+ -1 (len (double-rewrite poly1))))))) 
  :hints (("Goal" 
           :use car-last-compose-polys=expt-a))) 

(defthm 
  car-last-compose-polys-summary 
  (implies (and (polynomial-p poly1) 
                (polynomial-p poly2)) 
           (equal (car (last (compose-polynomials poly1 poly2))) 
                  (cond ((atom (double-rewrite poly1)) nil) 
                        ((atom (double-rewrite poly2)) 
                         (car (double-rewrite poly1))) 
                        ((atom (cdr (double-rewrite poly1))) 
                         (car (double-rewrite poly1))) 
                        ((atom (cdr (double-rewrite poly2))) 
                         (eval-polynomial poly1 (car (double-rewrite poly2)))) 
                        (t (* (car (last (double-rewrite poly1))) 
                              (expt (car (last (double-rewrite poly2))) 
                                    (+ -1 (len (double-rewrite poly1))))))))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION COMPOSE-POLYNOMIALS) 
                               car-last-compose-polys=eval-poly) 
           :use car-last-compose-polys=eval-poly))) 

(defun 
    compose-poly-with_-x (poly) 
  (compose-polynomials poly (list 0 -1))) 

(defthm 
  polynomial-p-compose-poly-with_-x 
  (implies (polynomial-p poly) 
           (polynomial-p (compose-poly-with_-x poly)))) 

(defthm 
  integer-listp-compose-poly-with_-x 
  (implies (integer-listp poly) 
           (integer-listp (compose-poly-with_-x poly)))) 

(defthm 
  rational-listp-compose-poly-with_-x 
  (implies (rational-listp poly) 
           (rational-listp (compose-poly-with_-x poly)))) 

(defthm 
  eval-polynomial-compose-poly-with_-x 
  (equal (eval-polynomial (compose-poly-with_-x poly) x) 
         (eval-polynomial poly (- x)))) 

(defthm 
  len-compose-poly-with_-x 
  (equal (len (compose-poly-with_-x poly)) 
         (len (double-rewrite poly)))) 

(defthm 
  car-last-compose-poly-with_-x 
  (implies (polynomial-p poly) 
           (equal (car (last (compose-poly-with_-x poly))) 
                  (cond ((atom (double-rewrite poly)) nil) 
                        ((atom (cdr (double-rewrite poly))) 
                         (car (double-rewrite poly))) 
                        (t (* (car (last (double-rewrite poly))) 
                              (expt -1 
                                    (+ -1 (len (double-rewrite poly))))))))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION COMPOSE-POLYNOMIALS))))) 

(defthm 
  eval-polynomial-compose-poly-with_-x-minus=0 
  (equal (equal (eval-polynomial (compose-poly-with_-x poly)(- z)) 0) 
         (equal (eval-polynomial poly z) 0))) 

(defthm 
  polynomial-zero-p-compose-poly-with_-x-minus=polynomial-zero-p 
  (implies (acl2-numberp z) 
           (equal (polynomial-zero-p (compose-poly-with_-x poly)(- z)) 
                  (polynomial-zero-p poly z)))) 

(defun 
    compose-poly-with_x^2 (poly) 
  (compose-polynomials poly (list 0 0 1))) 

(defthm 
  polynomial-p-compose-poly-with_x^2 
  (implies (polynomial-p poly) 
           (polynomial-p (compose-poly-with_x^2 poly)))) 

(defthm 
  integer-listp-compose-poly-with_x^2 
  (implies (integer-listp poly) 
           (integer-listp (compose-poly-with_x^2 poly)))) 

(defthm 
  rational-listp-compose-poly-with_x^2 
  (implies (rational-listp poly) 
           (rational-listp (compose-poly-with_x^2 poly)))) 

(defthm 
  eval-polynomial-compose-poly-with_x^2 
  (equal (eval-polynomial (compose-poly-with_x^2 poly) x) 
         (eval-polynomial poly (expt x 2)))) 

(defthm 
  len-compose-poly-with_x^2 
  (equal (len (compose-poly-with_x^2 poly)) 
         (cond ((atom (double-rewrite poly)) 0) 
               ((atom (cdr (double-rewrite poly))) 1) 
               (t (+ -1 (* 2 (len (double-rewrite poly))))))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION COMPOSE-POLYNOMIALS))))) 

(defthm 
  car-last-compose-poly-with_x^2 
  (implies (polynomial-p poly) 
           (equal (car (last (compose-poly-with_x^2 poly))) 
                  (if (consp (double-rewrite poly)) 
                      (car (last (double-rewrite poly))) 
                    nil))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION COMPOSE-POLYNOMIALS))))) 

(defthm 
  eval-polynomial-compose-poly-with_x^2=0 
  (equal (equal (eval-polynomial (compose-poly-with_x^2 poly) z) 0) 
         (equal (eval-polynomial poly (expt z 2)) 0))) 

(defthm 
  poly-zero-p-compose-poly-with_x^2=poly-zero-p-sqr 
  (implies (acl2-numberp z) 
           (equal (polynomial-zero-p (compose-poly-with_x^2 poly) z) 
                  (polynomial-zero-p poly (expt z 2))))) 

#+:non-standard-analysis 
(defthm 
  eval-polynomial-compose-poly-with_x^2-sqrt=0 
  (implies (and (realp z) 
                (>= z 0)) 
           (equal (equal (eval-polynomial (compose-poly-with_x^2 poly)(acl2-sqrt z)) 0) 
                  (equal (eval-polynomial poly z) 0)))) 

#+:non-standard-analysis 
(defthm 
  poly-zero-p-compose-poly-with_x^2-sqrt=poly-zero-p 
  (implies (and (realp z) 
                (>= z 0)) 
           (equal (polynomial-zero-p (compose-poly-with_x^2 poly)(acl2-sqrt z)) 
                  (polynomial-zero-p poly z)))) 

#+:non-standard-analysis 
(defthm 
  eval-polynomial-compose-poly-with_x^2-sqrt=0-a 
  (implies (and (realp z) 
                (< z 0)) 
           (equal (equal (eval-polynomial (compose-poly-with_x^2 poly) 
                                          (* (acl2-sqrt (- z)) #C(0 1))) 
                         0) 
                  (equal (eval-polynomial poly z) 0)))) 

#+:non-standard-analysis 
(defthm 
  poly-zero-p-compose-poly-with_x^2-sqrt=poly-zero-p-a 
  (implies (and (realp z) 
                (< z 0)) 
           (equal (polynomial-zero-p (compose-poly-with_x^2 poly) 
                                     (* (acl2-sqrt (- z)) #C(0 1))) 
                  (polynomial-zero-p poly z)))) 

(defun 
    compose-poly-with_x+d (poly d) 
  (compose-polynomials poly (list d 1))) 

(defthm 
  polynomial-p-compose-poly-with_x+d 
  (implies (polynomial-p poly) 
           (polynomial-p (compose-poly-with_x+d poly d)))) 

(defthm 
  integer-listp-compose-poly-with_x+d 
  (implies (and (integer-listp poly) 
                (integerp d)) 
           (integer-listp (compose-poly-with_x+d poly d)))) 

(defthm 
  rational-listp-compose-poly-with_x+d 
  (implies (and (rational-listp poly) 
                (rationalp d)) 
           (rational-listp (compose-poly-with_x+d poly d)))) 

(defthm 
  eval-polynomial-compose-poly-with_x+d 
  (equal (eval-polynomial (compose-poly-with_x+d poly d) x) 
         (eval-polynomial poly (+ x d)))) 

(defthm 
  len-compose-poly-with_x+d 
  (equal (len (compose-poly-with_x+d poly d)) 
         (len (double-rewrite poly)))) 

(defthm 
  consp-compose-poly-with_x+d 
  (equal (consp (compose-poly-with_x+d poly d)) 
         (consp (double-rewrite poly)))) 

(defthm 
  car-last-compose-poly-with_x+d 
  (implies (and (polynomial-p poly) 
                (acl2-numberp d)) 
           (equal (car (last (compose-poly-with_x+d poly d))) 
                  (if (consp (double-rewrite poly)) 
                      (car (last (double-rewrite poly))) 
                    nil))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION COMPOSE-POLYNOMIALS))))) 

(defthm 
  eval-polynomial-compose-poly-with_x+d_x-d=0 
  (equal (equal (eval-polynomial (compose-poly-with_x+d poly d)(+ z (- d))) 0) 
         (equal (eval-polynomial poly z) 0))) 

(defthm 
  polynomial-zero-p-compose-poly-with_x+d_x-d=polynomial-zero-p 
  (implies (acl2-numberp z) 
           (equal (polynomial-zero-p (compose-poly-with_x+d poly d)(+ z (- d))) 
                  (polynomial-zero-p poly z)))) 

;; See below: 
;; alt-minus=compose-poly-with_-x 
(defun 
    alt-minus (lst) 
  (declare (xargs :measure (len lst))) 
  (if (consp lst) 
      (cons (car lst)(alt-minus (polynomial-- (cdr lst)))) 
    lst)) 

(defthm 
  polynomial-*-list_0_-1 
  (equal (polynomial-* (list 0 -1) lst) 
         (if (consp (double-rewrite lst)) 
             (cons 0 (polynomial-- lst)) 
           (list 0 0)))) 

(defthm 
  compose-polys-poly--_list_0_-1 
  (equal (compose-polynomials (polynomial-- lst)(list 0 -1)) 
         (polynomial-- (compose-polynomials lst (list 0 -1))))) 

(defthmD 
  alt-minus=compose-poly-with_-x 
  (implies (acl2-number-listp lst) 
           (equal (alt-minus lst) 
                  (compose-poly-with_-x lst)))) 

(defthm 
  consp-alt-minus 
  (equal (consp (alt-minus lst)) 
         (consp (double-rewrite lst)))) 

(defthm 
  len-alt-minus 
  (equal (len (alt-minus lst)) 
         (len (double-rewrite lst)))) 

(defun 
    append-leading-zero (lst) 
  (declare (xargs :guard t)) 
  (if (consp lst) 
      (cons (car lst) 
            (append-leading-zero (cdr lst))) 
    (list 0))) 

(defthm 
  polynomial-p-append-leading-zero 
  (implies (polynomial-p poly) 
           (polynomial-p (append-leading-zero poly)))) 

(defthm 
  eval-polynomial-append-leading-zero 
  (equal (eval-polynomial (append-leading-zero poly) z) 
         (eval-polynomial poly z))) 

(defthm 
  len-append-leading-zero 
  (equal (len (append-leading-zero lst)) 
         (+ 1 (len (double-rewrite lst))))) 

;; See below: 
;; shift-polynomial=compose-poly-with_x+d 
(defun 
    shift-polynomial (poly dx) 
  (if (consp poly) 
      (add-const-polynomial 
       (polynomial-+ (append-leading-zero (scale-polynomial 
                                           (shift-polynomial (cdr poly) dx) 
                                           dx)) 
                     (cons 0 (shift-polynomial (cdr poly) dx))) 
       (car poly)) 
    nil)) 

(defthm 
  scale-polynomial_lst_1=lst 
  (implies (acl2-number-listp lst) 
           (equal (scale-polynomial lst 1) 
                  lst))) 

(defthm 
  acl2-number-listp-shift-polynomial 
  (acl2-number-listp (shift-polynomial poly dx))) 

(defthm 
  polynomial-+_poly_zero=poly-a 
  (implies (and (acl2-number-listp poly) 
                (consp poly)) 
           (equal (polynomial-+ poly (list 0)) 
                  poly))) 

(defthm 
  len-shift-polynomial 
  (equal (len (shift-polynomial poly dx)) 
         (len (double-rewrite poly)))) 

(defthm 
  polynomial-+-append-leading-zero 
  (implies (and (acl2-number-listp poly2) 
                (< (len (double-rewrite poly1)) 
                   (len (double-rewrite poly2)))) 
           (equal (polynomial-+ (append-leading-zero poly1) 
                                poly2) 
                  (polynomial-+ poly1 
                                poly2)))) 

(defthmD 
  shift-polynomial=compose-poly-with_x+d 
  (implies (acl2-number-listp poly) 
           (equal (shift-polynomial poly d) 
                  (compose-poly-with_x+d poly d)))) 

(defthm 
  polynomial-p-shift-polynomial 
  (polynomial-p (shift-polynomial poly dx))) 

(defthm 
  eval-polynomial-shift-polynomial 
  (equal (eval-polynomial (shift-polynomial poly dx) z) 
         (eval-polynomial poly (+ z dx)))) 

;; Divide poly by x+a: 
;; poly = r + q*(x+a) 
;; return (cons r q) [or NIL, if poly is an atom] 
(defun 
    divide-polynomial-with-remainder-by-x+a (poly a) 
  (if (consp poly) 
      (let ((rest (divide-polynomial-with-remainder-by-x+a (cdr poly) a))) 
        (if (consp rest) 
            (cons (- (car poly) 
                     (* a (car rest))) 
                  rest) 
          (list (car poly)))) 
    nil)) 
;;=============== 
;; (divide-polynomial-with-remainder-by-x+a '(3 2 1) -1) => (6 3 1) 
;; 3+2x+x^2 = 6 + (3+x)*(x+(-1)) 
;; (divide-polynomial-with-remainder-by-x+a '(3 2 1) 2) => (3 0 1) 
;; 3+2x+x^2 = 3 + (0+x)*(x+2) 
;; (divide-polynomial-with-remainder-by-x+a '(3 2 1) 1) => (2 1 1) 
;; 3+2x+x^2 = 2 + (1+x)(x+1) 
;; (divide-polynomial-with-remainder-by-x+a '(-6 -1 1) 2) => (0 -3 1) 
;; -6-x+x^2 = 0 + (-3+x)(x+2) 
;; (divide-polynomial-with-remainder-by-x+a '(3) 2) => (3) 
;; 3 = 3 + NIL*(x+2) [NIL represents the zero polynomial] 
;; (divide-polynomial-with-remainder-by-x+a nil 2) => NIL 
;; nil = NIL + NIL*(x+2) [NIL represents the zero polynomial] 
;; [(car NIL)=>NIL & (cdr NIL)=>NIL] 
;;=============== 

(defthm 
  polynomial-p-divide-poly-by-x+a 
  (implies (polynomial-p poly) 
           (polynomial-p (divide-polynomial-with-remainder-by-x+a poly a)))) 

(defthm 
  integer-listp-divide-poly-by-x+a 
  (implies (and (integer-listp poly) 
                (integerp a)) 
           (integer-listp (divide-polynomial-with-remainder-by-x+a poly a)))) 

(defthm 
  rational-listp-divide-poly-by-x+a 
  (implies (and (rational-listp poly) 
                (rationalp a)) 
           (rational-listp (divide-polynomial-with-remainder-by-x+a poly a)))) 

#+:non-standard-analysis 
(defthm 
  real-listp-divide-poly-by-x+a 
  (implies (and (real-listp poly) 
                (realp a)) 
           (real-listp (divide-polynomial-with-remainder-by-x+a poly a)))) 

(defthm 
  acl2-number-listp-divide-poly-by-x+a 
  (implies (acl2-number-listp poly) 
           (acl2-number-listp (divide-polynomial-with-remainder-by-x+a poly a)))) 

(defthm 
  consp-divide-poly-by-x+a=consp 
  (equal (consp (divide-polynomial-with-remainder-by-x+a poly a)) 
         (consp (double-rewrite poly)))) 

(defthm 
  len-divide-poly-by-x+a=len 
  (equal (len (divide-polynomial-with-remainder-by-x+a poly a)) 
         (len (double-rewrite poly)))) 

(defthm 
  car-last-divide-poly-by-x+a=car-last 
  (equal (car (last (divide-polynomial-with-remainder-by-x+a poly a))) 
         (car (last (double-rewrite poly))))) 

(defthm 
  divide-zero-poly-by-x+a 
  (implies (zero-polynomial-p poly) 
           (equal (divide-polynomial-with-remainder-by-x+a poly a) 
                  poly))) 

(defthm 
  divide-constant-poly-by-x+a 
  (implies (constant-polynomial-p poly) 
           (equal (divide-polynomial-with-remainder-by-x+a poly a) 
                  poly))) 

(defthm 
  divide-poly-by-x+zerop 
  (implies (and (acl2-number-listp poly) 
                (zerop a)) 
           (equal (divide-polynomial-with-remainder-by-x+a poly a) 
                  poly))) 

;; (car (divide-polynomial-with-remainder-by-x+a poly a) 
;; is the remainder when poly is divided by x+a 
(defthm 
  acl2-numberp-car-divide-poly-by-x+a 
  (implies (and (acl2-number-listp poly) 
                (consp poly)) 
           (acl2-numberp (car (divide-polynomial-with-remainder-by-x+a poly a)))) 
  :rule-classes :type-prescription) 

;; (cdr (divide-polynomial-with-remainder-by-x+a poly a) 
;; is the quotient when poly is divided by x+a 
(defthm 
  polynomial-p-cdr-divide-poly-by-x+a 
  (implies (polynomial-p poly) 
           (polynomial-p (cdr (divide-polynomial-with-remainder-by-x+a poly a))))) 

(defthm 
  len-cdr-divide-poly-by-x+a 
  (equal (len (cdr (divide-polynomial-with-remainder-by-x+a poly a))) 
         (if (consp (double-rewrite poly)) 
             (+ -1 (len (double-rewrite poly))) 
           0))) 

(defthm 
  car-last-cdr-divide-poly-by-x+a=car-last 
  (implies (consp (cdr (double-rewrite poly))) 
           (equal (car (last (cdr (divide-polynomial-with-remainder-by-x+a poly a)))) 
                  (car (last (double-rewrite poly)))))) 

(defthm 
  car-last-cdr-divide-poly-by-x+a=car-last-A 
  (implies (< 1 (len (double-rewrite poly))) 
           (equal (car (last (cdr (divide-polynomial-with-remainder-by-x+a poly a)))) 
                  (car (last (double-rewrite poly)))))) 

(defthm 
  zero-poly-divide-poly-by-x+a=zero-poly 
  (implies (polynomial-p poly) 
           (equal (zero-polynomial-p (divide-polynomial-with-remainder-by-x+a poly a)) 
                  (zero-polynomial-p poly)))) 

(defthm 
  constant-poly-divide-poly-by-x+a=constant-poly 
  (implies (polynomial-p poly) 
           (equal (constant-polynomial-p (divide-polynomial-with-remainder-by-x+a poly a)) 
                  (constant-polynomial-p poly)))) 

(defthm 
  consp-cdr-for-not-constant-poly 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly))) 
           (consp (cdr poly)))) 

(defthm 
  consp-cdr-divide-poly-by-x+a-for-not-constant-poly 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly))) 
           (consp (cdr (divide-polynomial-with-remainder-by-x+a poly a))))) 

(defthm 
  len-divide-poly-by-x+a>1-for-not-constant-poly 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly))) 
           (< 1 (len (divide-polynomial-with-remainder-by-x+a poly a))))) 

(defthm 
  not-zero-poly-cdr-for-not-constant-poly 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly))) 
           (not (zero-polynomial-p (cdr poly))))) 

(defthm 
  not-zero-poly-cdr-divide-poly-by-x+a-for-not-constant-poly 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly))) 
           (not (zero-polynomial-p 
                 (cdr (divide-polynomial-with-remainder-by-x+a poly a)))))) 

(defthm 
  not-constant-poly-cdr-divide-poly-by-x+a 
  (implies (and (polynomial-p poly) 
                (not (zero-polynomial-p (cddr poly)))) 
           (not (constant-polynomial-p 
                 (cdr (divide-polynomial-with-remainder-by-x+a poly a)))))) 

(defthm 
  eval-divide-poly-by-x+a 
  (equal (+ (* (eval-polynomial (cdr (divide-polynomial-with-remainder-by-x+a poly a)) x) 
               (+ x a)) 
            (car (divide-polynomial-with-remainder-by-x+a poly a))) 
         (eval-polynomial poly x))) 

;; Remainder = 0 
;; when Divide poly by x-z 
;; iff 
;; z is a zero of poly 
(defthm 
  remainder=0_when-divide-poly-by_x-z=z-is-zero-of-poly 
  (implies (and (consp (double-rewrite poly)) 
                (polynomial-p poly)) 
           (equal (equal (car (divide-polynomial-with-remainder-by-x+a poly (- z))) 0) 
                  (equal (eval-polynomial poly z) 0))) 
  :hints (("Goal" 
           :in-theory (disable eval-divide-poly-by-x+a) 
           :use (:instance 
                 eval-divide-poly-by-x+a 
                 (x z) 
                 (a (- z)))))) 

(defthm 
  other-zeros-also-zeros-of-quotient 
  (implies (and (consp (double-rewrite poly)) 
                (polynomial-p poly) 
                (equal (eval-polynomial poly a) 0) 
                (equal (eval-polynomial poly b) 0) 
                (acl2-numberp a) 
                (acl2-numberp b) 
                (not (equal a b))) 
           (equal (eval-polynomial (cdr (divide-polynomial-with-remainder-by-x+a poly (- a))) 
                                   b) 
                  0)) 
  :hints (("Goal" 
           :in-theory (disable remainder=0_when-divide-poly-by_x-z=z-is-zero-of-poly 
                               eval-divide-poly-by-x+a) 
           :use ((:instance remainder=0_when-divide-poly-by_x-z=z-is-zero-of-poly 
                            (z a)) 
                 (:instance eval-divide-poly-by-x+a 
                            (a (- a)) 
                            (x b)) 
                 (:instance (:theorem (implies (and (acl2-numberp x) 
                                                    (acl2-numberp y) 
                                                    (equal (* x y) 0) 
                                                    (not (equal y 0))) 
                                               (equal x 0))) 
                            (x (eval-polynomial 
                                (cdr (divide-polynomial-with-remainder-by-x+a poly (- a))) 
                                b)) 
                            (y (+ b (- a)))))))) 

;; Linear Poly is a polynomial of degree 1: 
;; (cons a1 (cons a2 zero-poly)) 
;; with not(a2=0). 
(defthm 
  eval-linear-poly 
  (implies (and (polynomial-p poly) 
                (consp (cdr (double-rewrite poly))) 
                (zero-polynomial-p (cddr poly))) 
           (equal (eval-polynomial poly x) 
                  (+ (car (double-rewrite poly)) 
                     (* x (cadr (double-rewrite poly))))))) 

(defthm 
  zeros-of-linear-poly-are-equal-lemma 
  (implies (and (acl2-numberp x) 
                (acl2-numberp y) 
                (not (equal y 0)) 
                (acl2-numberp a) 
                (acl2-numberp b) 
                (equal (+ x (* a y)) 
                       (+ x (* b y)))) 
           (equal a b)) 
  :rule-classes nil) 

(defthm 
  zeros-of-linear-poly-are-equal 
  (implies (and (zero-polynomial-p (cddr poly)) 
                (polynomial-p poly) 
                (consp (cdr (double-rewrite poly))) 
                (not (equal (cadr (double-rewrite poly)) 0)) 
                (acl2-numberp a) 
                (acl2-numberp b) 
                (equal (eval-polynomial poly a) 0) 
                (equal (eval-polynomial poly b) 0)) 
           (equal (equal a b) t)) 
  :hints (("Goal" 
           :use ((:instance zeros-of-linear-poly-are-equal-lemma 
                            (x (car poly)) 
                            (y (cadr poly))) 
                 (:instance (:theorem (implies (and (equal p r) 
                                                    (equal q r)) 
                                               (equal p q))) 
                            (p (+ (car poly)(* a (cadr poly)))) 
                            (q (+ (car poly)(* b (cadr poly)))) 
                            (r 0)))))) 

;; z is a zero of nonconstant poly. 
(defun 
    nonconstant-polynomial-zero-p (poly z) 
  (and (not (constant-polynomial-p poly)) 
       (polynomial-zero-p poly z))) 

(defthm 
  other-zeros-of-nonconstant-also-zeros-of-nonconstant-quotient 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly)) 
                (polynomial-zero-p poly a) 
                (polynomial-zero-p poly b) 
                (not (equal a b))) 
           (nonconstant-polynomial-zero-p 
            (cdr (divide-polynomial-with-remainder-by-x+a poly (- a))) 
            b)) 
  :hints (("Goal" 
           :in-theory (disable other-zeros-also-zeros-of-quotient) 
           :use other-zeros-also-zeros-of-quotient 
           :cases ((zero-polynomial-p (cddr poly)))))) 

;; For lst = (a1 ... an), 
;; Divide poly by (x-a1)*...*(x-an) 
;; Return only quotient polynomial 
(defun 
    divide-polynomial-by-list (poly lst) 
  (if (consp lst) 
      (divide-polynomial-by-list (cdr (divide-polynomial-with-remainder-by-x+a poly 
                                                                               (- (car lst)))) 
                                 (cdr lst)) 
    poly)) 
#|============================== 
(divide-polynomial-by-list '(3 2 1) '(1)) => (3 1) 
3+2x+x^2 / x-1 = 3+x [quotient only] 
(divide-polynomial-by-list '(3 1) '(1)) => (1) 
3+x / x-1 = 1 [quotient only] 
(divide-polynomial-by-list '(3 2 1) '(1 1)) => (1) 
3+2x+x^2 / (x-1)(x-1) = 1 [quotient only] 
(divide-polynomial-by-list '(6 -7 0 1) '(1 2)) => (3 1) 
6-7x+x^3 / (x-1)(x-2) = 3+x 
(divide-polynomial-by-list '(6 -7 0 1) '(2 1)) => (3 1) 
6-7x+x^3 / (x-2)(x-1) = 3+x 
(divide-polynomial-by-list '(6 -7 0 1) '(-2 1)) => (-1 1) 
6-7x+x^3 / (x+2)(x-1) = -1+x [quotient only] 
(divide-polynomial-by-list '(6 -7 0 1) '(1 -2)) => (-1 1) 
6-7x+x^3 / (x-1)(x+2) = -1+x [quotient only] 
(divide-polynomial-by-list '(6 -7 0 1) '(1 1 1 1)) => NIL 
(divide-polynomial-by-list '(6 -7 0 1) '(1 1 1 1 1 1)) => NIL 
===================|# 

(defthm 
  len-divide-polynomial-by-list 
  (implies (< (len (double-rewrite lst)) 
              (len (double-rewrite poly))) 
           (equal (len (divide-polynomial-by-list poly lst)) 
                  (- (len (double-rewrite poly)) 
                     (len (double-rewrite lst)))))) 

(defthm 
  divide-polynomial-by-list=nil 
  (implies (and (polynomial-p poly) 
                (>= (len (double-rewrite lst)) 
                    (len (double-rewrite poly)))) 
           (equal (divide-polynomial-by-list poly lst) 
                  nil))) 

(defthm 
  polynomial-p-divide-polynomial-by-list 
  (implies (polynomial-p poly) 
           (polynomial-p (divide-polynomial-by-list poly lst)))) 

;; lst is a list of distinct zeros of nonconstant poly 
(defun 
    distinct-nonconstant-polynomial-zero-list-p (poly lst) 
  (if (consp lst) 
      (and (nonconstant-polynomial-zero-p poly (car lst)) 
           (not (member-equal (car lst)(cdr lst))) 
           (distinct-nonconstant-polynomial-zero-list-p poly (cdr lst))) 
    (null lst))) 

(defthm 
  list-of-distinct-zeros-is-list-of-acl2-numberps 
  (implies (distinct-nonconstant-polynomial-zero-list-p poly lst) 
           (acl2-number-listp lst)) 
  :rule-classes :forward-chaining) 

(defthm 
  list-of-distinct-zeros-contains-only-zeros 
  (implies (and (distinct-nonconstant-polynomial-zero-list-p poly lst) 
                (member-equal x (double-rewrite lst))) 
           (equal (eval-polynomial poly x) 0))) 

(defthm 
  no-duplicates-in-list-of-distinct-zeros 
  (implies (distinct-nonconstant-polynomial-zero-list-p poly lst) 
           (no-duplicatesp-equal lst))) 

(defthm 
  distinct-nonconstant-stepper-lemma-a 
  (IMPLIES (AND (NOT (MEMBER-EQUAL A (double-rewrite LST))) 
                (ACL2-NUMBERP A) 
                (POLYNOMIAL-P POLY) 
                (EQUAL (EVAL-POLYNOMIAL POLY A) 0) 
                (DISTINCT-NONCONSTANT-POLYNOMIAL-ZERO-LIST-P POLY LST) 
                (IMPLIES (AND (POLYNOMIAL-P POLY) 
                              (DISTINCT-NONCONSTANT-POLYNOMIAL-ZERO-LIST-P POLY (CDR LST)) 
                              (NONCONSTANT-POLYNOMIAL-ZERO-P POLY A) 
                              (NOT (MEMBER-EQUAL A (CDR (double-rewrite LST))))) 
                         (DISTINCT-NONCONSTANT-POLYNOMIAL-ZERO-LIST-P 
                          (CDR (DIVIDE-POLYNOMIAL-WITH-REMAINDER-BY-X+A POLY (- A))) 
                          (CDR LST)))) 
           (DISTINCT-NONCONSTANT-POLYNOMIAL-ZERO-LIST-P 
            (CDR (DIVIDE-POLYNOMIAL-WITH-REMAINDER-BY-X+A POLY (- A))) 
            (cdr LST)))) 

(defthm 
  distinct-nonconstant-stepper-lemma-b 
  (IMPLIES (AND (NOT (MEMBER-EQUAL A (double-rewrite LST))) 
                (ACL2-NUMBERP (CAR LST)) 
                (ACL2-NUMBERP A) 
                (POLYNOMIAL-P POLY) 
                (NOT (CONSTANT-POLYNOMIAL-P POLY)) 
                (EQUAL (EVAL-POLYNOMIAL POLY (CAR LST)) 0) 
                (EQUAL (EVAL-POLYNOMIAL POLY A) 0)) 
           (NONCONSTANT-POLYNOMIAL-ZERO-P 
            (CDR (DIVIDE-POLYNOMIAL-WITH-REMAINDER-BY-X+A POLY (- A))) 
            (CAR LST))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION CONSTANT-POLYNOMIAL-P) 
                               other-zeros-of-nonconstant-also-zeros-of-nonconstant-quotient) 
           :use (:instance 
                 other-zeros-of-nonconstant-also-zeros-of-nonconstant-quotient 
                 (b (car lst)))))) 

(defthm 
  distinct-nonconstant-stepper 
  (implies (and (polynomial-p poly) 
                (distinct-nonconstant-polynomial-zero-list-p poly lst) 
                (nonconstant-polynomial-zero-p poly a) 
                (not (member-equal a (double-rewrite lst)))) 
           (distinct-nonconstant-polynomial-zero-list-p 
            (cdr (divide-polynomial-with-remainder-by-x+a poly (- a))) 
            lst)) 
  :hints (("Goal" 
           :induct (distinct-nonconstant-polynomial-zero-list-p poly lst)))) 

(defthm 
  nonconst-zeros-of-quotient-list-lemma-A 
  (IMPLIES (AND (CONSP (double-rewrite LST)) 
                (POLYNOMIAL-P POLY) 
                (DISTINCT-NONCONSTANT-POLYNOMIAL-ZERO-LIST-P POLY LST) 
                (EQUAL (EVAL-POLYNOMIAL POLY A) 0) 
                (ACL2-NUMBERP A) 
                (NOT (MEMBER-EQUAL A (double-rewrite LST)))) 
           (NOT (CONSTANT-POLYNOMIAL-P 
                 (CDR (DIVIDE-POLYNOMIAL-WITH-REMAINDER-BY-X+A POLY (- (CAR LST))))))) 
  :hints (("Goal" 
           :in-theory (disable zeros-of-linear-poly-are-equal) 
           :use (:instance 
                 zeros-of-linear-poly-are-equal 
                 (b (car lst)))))) 

(defthm 
  nonconst-zeros-of-quotient-list-lemma-B 
  (IMPLIES (AND (CONSP (double-rewrite LST)) 
                (POLYNOMIAL-P POLY) 
                (DISTINCT-NONCONSTANT-POLYNOMIAL-ZERO-LIST-P POLY LST) 
                (ACL2-NUMBERP A) 
                (EQUAL (EVAL-POLYNOMIAL POLY A) 0) 
                (NOT (MEMBER-EQUAL A (double-rewrite LST)))) 
           (POLYNOMIAL-ZERO-P 
            (CDR (DIVIDE-POLYNOMIAL-WITH-REMAINDER-BY-X+A POLY (- (CAR LST)))) 
            A)) 
  :hints (("Goal" 
           :in-theory (disable OTHER-ZEROS-OF-NONCONSTANT-ALSO-ZEROS-OF-NONCONSTANT-QUOTIENT) 
           :use (:instance 
                 OTHER-ZEROS-OF-NONCONSTANT-ALSO-ZEROS-OF-NONCONSTANT-QUOTIENT 
                 (a (car lst)) 
                 (b a))))) 

(defthm 
  nonconst-zeros-of-quotient-list-lemma-C 
  (IMPLIES (AND (CONSP (double-rewrite LST)) 
                (POLYNOMIAL-P POLY) 
                (DISTINCT-NONCONSTANT-POLYNOMIAL-ZERO-LIST-P POLY LST) 
                (ACL2-NUMBERP A) 
                (EQUAL (EVAL-POLYNOMIAL POLY A) 0) 
                (NOT (MEMBER-EQUAL A (double-rewrite LST))) 
                (IMPLIES (AND (POLYNOMIAL-P 
                               (CDR (DIVIDE-POLYNOMIAL-WITH-REMAINDER-BY-X+A POLY (- (CAR LST))))) 
                              (NOT 
                               (CONSTANT-POLYNOMIAL-P 
                                (CDR (DIVIDE-POLYNOMIAL-WITH-REMAINDER-BY-X+A POLY (- (CAR LST)))))) 
                              (POLYNOMIAL-ZERO-P 
                               (CDR (DIVIDE-POLYNOMIAL-WITH-REMAINDER-BY-X+A POLY (- (CAR LST)))) 
                               A) 
                              (DISTINCT-NONCONSTANT-POLYNOMIAL-ZERO-LIST-P 
                               (CDR (DIVIDE-POLYNOMIAL-WITH-REMAINDER-BY-X+A POLY (- (CAR LST)))) 
                               (CDR LST)) 
                              (NOT (MEMBER-EQUAL A (CDR LST)))) 
                         (NONCONSTANT-POLYNOMIAL-ZERO-P 
                          (DIVIDE-POLYNOMIAL-BY-LIST 
                           (CDR (DIVIDE-POLYNOMIAL-WITH-REMAINDER-BY-X+A POLY (- (CAR LST)))) 
                           (CDR LST)) 
                          A))) 
           (NONCONSTANT-POLYNOMIAL-ZERO-P 
            (DIVIDE-POLYNOMIAL-BY-LIST 
             (CDR (DIVIDE-POLYNOMIAL-WITH-REMAINDER-BY-X+A POLY (- (CAR LST)))) 
             (CDR LST)) 
            A))) 

(defthm 
  other-nonconstant-zeros-also-nonconstant-zeros-of-quotient-list 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly)) 
                (polynomial-zero-p poly a) 
                (distinct-nonconstant-polynomial-zero-list-p poly lst) 
                (not (member-equal a (double-rewrite lst)))) 
           (nonconstant-polynomial-zero-p (divide-polynomial-by-list poly lst) 
                                          a)) 
  :hints (("Goal" 
           :induct (divide-polynomial-by-list poly lst)))) 

(defthm 
  divide-nil-by-list 
  (equal (divide-polynomial-by-list nil lst) 
         nil)) 

(defthm 
  len-divide-polynomial-by-list-2 
  (implies (< 1 (len (divide-polynomial-by-list poly lst))) 
           (equal (len (divide-polynomial-by-list poly lst)) 
                  (- (len (double-rewrite poly)) 
                     (len (double-rewrite lst)))))) 

(defthm 
  nbr-distinct-zeros<len-poly-lemma 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly)) 
                (distinct-nonconstant-polynomial-zero-list-p poly lst) 
                (polynomial-zero-p poly a) 
                (not (member-equal a lst))) 
           (< (+ 1 (len lst))(len poly))) 
  :rule-classes nil 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION CONSTANT-POLYNOMIAL-P) 
                               NOT-CONSTANT-POLYNOMIAL-HAS-LEN-2+ 
                               len-divide-polynomial-by-list-2 
                               other-nonconstant-zeros-also-nonconstant-zeros-of-quotient-list) 
           :use (len-divide-polynomial-by-list-2 
                 other-nonconstant-zeros-also-nonconstant-zeros-of-quotient-list 
                 (:instance NOT-CONSTANT-POLYNOMIAL-HAS-LEN-2+ 
                            (poly (divide-polynomial-by-list poly lst))))))) 

(defthm 
  nbr-distinct-zeros<len-poly 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly)) 
                (distinct-nonconstant-polynomial-zero-list-p poly lst)) 
           (< (len lst)(len poly))) 
  :hints (("Goal" 
           :use (:instance nbr-distinct-zeros<len-poly-lemma 
                           (a (car lst)) 
                           (lst (cdr lst)))))) 

(defchoose 
  choose-new-zero (x) (poly lst) 
  (and (polynomial-zero-p poly x) 
       (not (member-equal x lst)))) 

(defun-sk 
  exists-another-zero (poly lst) 
  (exists x 
          (and (polynomial-zero-p poly x) 
               (not (member x lst))))) 

(defun 
    choose-n-distinct-zeros (n poly lst) 
  (if (zp n) 
      lst 
    (if (exists-another-zero poly lst) 
        (choose-n-distinct-zeros (+ -1 n) 
                                 poly 
                                 (cons (choose-new-zero poly lst) 
                                       lst)) 
      lst))) 

(defthm 
  choose-new-zero-valid 
  (implies (exists-another-zero poly lst) 
           (and (polynomial-zero-p poly (choose-new-zero poly lst)) 
                (not (member-equal (choose-new-zero poly lst) lst)))) 
  :hints (("Goal" 
           :use ((:instance 
                  choose-new-zero 
                  (x (exists-another-zero-witness poly lst))))))) 

(defthm 
  choose-n-distinct-zeros-valid 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly)) 
                (distinct-nonconstant-polynomial-zero-list-p poly lst)) 
           (distinct-nonconstant-polynomial-zero-list-p poly 
                                                        (choose-n-distinct-zeros n poly lst)))) 

(defthm 
  acl2-numberp-choose-new-zero 
  (implies (exists-another-zero poly lst) 
           (acl2-numberp (choose-new-zero poly lst))) 
  :hints (("Goal" 
           :in-theory (disable choose-new-zero-valid) 
           :use choose-new-zero-valid))) 

(defthm 
  len-choose-n-distinct-zeros 
  (implies (natp n) 
           (<= (len (choose-n-distinct-zeros n poly lst)) 
               (+ n (len lst))))) 

(defun 
    find-distinct-zeros-of-poly (poly) 
  (choose-n-distinct-zeros (+ -1 (len poly)) poly nil)) 

(defthm 
  find-distinct-zeros-of-poly-contains-only-zeros-A 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly))) 
           (distinct-nonconstant-polynomial-zero-list-p poly 
                                                        (find-distinct-zeros-of-poly poly)))) 

(defthm 
  choose-n-distinct-zeros-contains-all-zeros-case-1 
  (implies (and (natp n) 
                (< (len (choose-n-distinct-zeros n poly lst)) 
                   (+ n (len (double-rewrite lst))))) 
           (not (exists-another-zero poly (choose-n-distinct-zeros n poly lst))))) 

(defthm 
  find-distinct-zeros-of-poly-contains-all-zeros-case-1-lemma 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly)) 
                (< (length (find-distinct-zeros-of-poly poly)) 
                   (+ -1 (len (double-rewrite poly))))) 
           (not (exists-another-zero poly (find-distinct-zeros-of-poly poly))))) 

(defthm 
  no-more-zeros-when-not-exists-another-zero 
  (implies (and (not (member-equal x lst)) 
                (not (exists-another-zero poly lst))) 
           (not (polynomial-zero-p poly x))) 
  :hints (("Goal" 
           :in-theory (disable exists-another-zero-suff) 
           :use exists-another-zero-suff))) 

(defthm 
  find-distinct-zeros-of-poly-contains-all-zeros-case-1 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly)) 
                (< (len (find-distinct-zeros-of-poly poly)) 
                   (+ -1 (len (double-rewrite poly)))) 
                (not (member-equal x (find-distinct-zeros-of-poly poly)))) 
           (not (polynomial-zero-p poly x))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION FIND-distinct-ZEROS-OF-POLY) 
                               (:DEFINITION POLYNOMIAL-ZERO-P))))) 

(defthm 
  find-distinct-zeros-of-poly-contains-all-zeros-case-2 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly)) 
                (equal (len (find-distinct-zeros-of-poly poly)) 
                       (+ -1 (len (double-rewrite poly)))) 
                (not (member-equal x (find-distinct-zeros-of-poly poly)))) 
           (not (polynomial-zero-p poly x))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION POLYNOMIAL-ZERO-P) 
                               (:DEFINITION CHOOSE-N-distinct-ZEROS) 
                               nbr-distinct-zeros<len-poly) 
           :use (:instance nbr-distinct-zeros<len-poly 
                           (lst (cons x (find-distinct-zeros-of-poly poly))))))) 

(defthm 
  find-distinct-zeros-of-poly-contains-all-zeros-case-3 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly)) 
                (> (len (find-distinct-zeros-of-poly poly)) 
                   (+ -1 (len (double-rewrite poly))))) 
           (not (polynomial-zero-p poly x))) 
  :hints (("Goal" 
           :in-theory (disable nbr-distinct-zeros<len-poly) 
           :use (:instance nbr-distinct-zeros<len-poly 
                           (lst (find-distinct-zeros-of-poly poly)))))) 

(defthm 
  find-distinct-zeros-of-poly-contains-all-zeros-A 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly)) 
                (polynomial-zero-p poly x)) 
           (member-equal x (find-distinct-zeros-of-poly poly))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION FIND-distinct-ZEROS-OF-POLY) 
                               (:DEFINITION CONSTANT-POLYNOMIAL-P) 
                               (:DEFINITION POLYNOMIAL-ZERO-P)) 
           :cases ((equal (len (find-distinct-zeros-of-poly poly)) 
                          (+ -1 (len poly))) 
                   (< (len (find-distinct-zeros-of-poly poly)) 
                      (+ -1 (len poly))) 
                   (> (len (find-distinct-zeros-of-poly poly)) 
                      (+ -1 (len poly))))))) 

(defthm 
  no-duplicates-in-find-distinct-zeros-of-poly-A 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly))) 
           (no-duplicatesp-equal (find-distinct-zeros-of-poly poly))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION FIND-distinct-ZEROS-OF-POLY) 
                               (:DEFINITION CONSTANT-POLYNOMIAL-P) 
                               find-distinct-zeros-of-poly-contains-only-zeros-A) 
           :use find-distinct-zeros-of-poly-contains-only-zeros-A))) 

(defthm 
  len-find-distinct-zeros-of-poly-A 
  (implies (and (polynomial-p poly) 
                (not (constant-polynomial-p poly))) 
           (< (len (find-distinct-zeros-of-poly poly)) 
              (len poly)))) 

(defthm 
  no-zeros-for-constant-nonzero-polys 
  (implies (and (constant-polynomial-p poly) 
                (not (zero-polynomial-p poly))) 
           (not (polynomial-zero-p poly x)))) 

(defthm 
  find-distinct-zeros-of-poly=nil 
  (implies (and (constant-polynomial-p poly) 
                (not (zero-polynomial-p poly))) 
           (equal (find-distinct-zeros-of-poly poly) 
                  nil))) 

(defthm 
  list-of-distinct-zeros-contains-only-zeros-A 
  (implies (and (distinct-nonconstant-polynomial-zero-list-p poly lst) 
                (member-equal x (double-rewrite lst))) 
           (polynomial-zero-p poly x))) 

(defthm 
  find-distinct-zeros-of-poly-contains-only-zeros 
  (implies (and (polynomial-p poly) 
                (not (zero-polynomial-p poly)) 
                (member-equal x (find-distinct-zeros-of-poly poly))) 
           (polynomial-zero-p poly x)) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION POLYNOMIAL-ZERO-P) 
                               (:DEFINITION ZERO-POLYNOMIAL-P) 
                               (:DEFINITION CONSTANT-POLYNOMIAL-P) 
                               (:DEFINITION FIND-DISTINCT-ZEROS-OF-POLY) 
                               FIND-DISTINCT-ZEROS-OF-POLY-CONTAINS-ONLY-ZEROS-A) 
           :use FIND-DISTINCT-ZEROS-OF-POLY-CONTAINS-ONLY-ZEROS-A))) 

(defthm 
  find-distinct-zeros-of-poly-contains-all-zeros 
  (implies (and (polynomial-p poly) 
                (not (zero-polynomial-p poly)) 
                (polynomial-zero-p poly x)) 
           (member-equal x (find-distinct-zeros-of-poly poly))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION POLYNOMIAL-ZERO-P) 
                               (:DEFINITION ZERO-POLYNOMIAL-P) 
                               (:DEFINITION CONSTANT-POLYNOMIAL-P) 
                               (:DEFINITION FIND-DISTINCT-ZEROS-OF-POLY) 
                               FIND-DISTINCT-ZEROS-OF-POLY-CONTAINS-ALL-ZEROS-A) 
           :use FIND-DISTINCT-ZEROS-OF-POLY-CONTAINS-ALL-ZEROS-A))) 

(defthm 
  no-duplicates-in-find-distinct-zeros-of-poly 
  (implies (and (polynomial-p poly) 
                (not (zero-polynomial-p poly))) 
           (no-duplicatesp-equal (find-distinct-zeros-of-poly poly))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION ZERO-POLYNOMIAL-P) 
                               (:DEFINITION CONSTANT-POLYNOMIAL-P) 
                               (:DEFINITION FIND-DISTINCT-ZEROS-OF-POLY) 
                               NO-DUPLICATES-IN-FIND-DISTINCT-ZEROS-OF-POLY-A) 
           :use NO-DUPLICATES-IN-FIND-DISTINCT-ZEROS-OF-POLY-A))) 

(defthm 
  len-find-distinct-zeros-of-poly 
  (implies (and (polynomial-p poly) 
                (not (zero-polynomial-p poly))) 
           (< (len (find-distinct-zeros-of-poly poly)) 
              (len poly))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION ZERO-POLYNOMIAL-P) 
                               (:DEFINITION CONSTANT-POLYNOMIAL-P) 
                               (:DEFINITION FIND-DISTINCT-ZEROS-OF-POLY) 
                               LEN-FIND-DISTINCT-ZEROS-OF-POLY-A) 
           :use LEN-FIND-DISTINCT-ZEROS-OF-POLY-A))) 

(in-theory (disable (:DEFINITION FIND-DISTINCT-ZEROS-OF-POLY) 
                    (:EXECUTABLE-COUNTERPART FIND-DISTINCT-ZEROS-OF-POLY))) 

(defun 
    truncate-polynomial (poly) 
  (declare (xargs :guard t)) 
  (if (consp poly) 
      (if (zero-polynomial-p poly) 
          nil 
        (cons (car poly) 
              (truncate-polynomial (cdr poly)))) 
    nil)) 

(defthm 
  polynomial-p-truncate-polynomial 
  (implies (polynomial-p poly) 
           (polynomial-p (truncate-polynomial poly)))) 

(defthm 
  integer-listp-truncate-polynomial 
  (implies (integer-listp poly) 
           (integer-listp (truncate-polynomial poly)))) 

(defthm 
  rational-listp-truncate-polynomial 
  (implies (rational-listp poly) 
           (rational-listp (truncate-polynomial poly)))) 

#+:non-standard-analysis 
(defthm 
  real-listp-truncate-polynomial 
  (implies (real-listp poly) 
           (real-listp (truncate-polynomial poly)))) 

(defthm 
  acl2-number-listp-truncate-polynomial 
  (implies (acl2-number-listp poly) 
           (acl2-number-listp (truncate-polynomial poly)))) 

(defthm 
  consp-truncate-polynomial 
  (implies (and (acl2-number-listp poly) 
                (not (zero-polynomial-p poly))) 
           (consp (truncate-polynomial poly))) 
  :rule-classes :type-prescription) 

(defthm 
  not_car-last-truncate-polynomial=0 
  (implies (and (acl2-number-listp poly) 
                (not (zero-polynomial-p poly))) 
           (not (equal (car (last (truncate-polynomial poly))) 
                       0)))) 

(defthm 
  truncate-polynomial_truncate-polynomial=truncate-polynomial 
  (implies (acl2-number-listp poly) 
           (equal (truncate-polynomial (truncate-polynomial poly)) 
                  (truncate-polynomial poly)))) 

(defthm 
  eval-truncate-polynomial 
  (equal (eval-polynomial (truncate-polynomial poly) z) 
         (eval-polynomial poly z))) 

(defthm 
  len-truncate-polynomial 
  (implies (and (acl2-number-listp poly) 
                (not (constant-polynomial-p poly))) 
           (< 1 (len (truncate-polynomial poly))))) 

(defun 
    dhnf-p (poly) 
  (if (consp poly) 
      (let ((fst (car poly)) 
            (rst (cdr poly))) 
        (if (consp rst) 
            (and (acl2-numberp fst) 
                 (dhnf-p rst)) 
          (and (null rst) 
               (acl2-numberp fst) 
               (not (zerop fst))))) 
    (null poly))) 

(defthm 
  NOT-car-last-dhnf-p=0 
  (implies (and (dhnf-p poly) 
                (consp (double-rewrite poly))) 
           (not (equal 0 (car (last poly)))))) 

(defthm 
  dhnf-p-forward-to-polynomial-p 
  (implies (dhnf-p poly) 
           (polynomial-p poly)) 
  :rule-classes :forward-chaining) 

(defthm 
  dhnf-p-truncate-polynomial 
  (implies (acl2-number-listp lst) 
           (dhnf-p (truncate-polynomial lst)))) 

(defthm 
  dhnf-p-polynomial-- 
  (implies (dhnf-p poly) 
           (dhnf-p (polynomial-- poly)))) 

(defthm 
  dhnf-p-scale-polynomial 
  (implies (and (dhnf-p poly) 
                (acl2-numberp c) 
                (not (equal 0 c))) 
           (dhnf-p (scale-polynomial poly c)))) 

(defthm 
  dhnf-p-polynomial-+-A 
  (implies (and (consp (double-rewrite poly1)) 
                (true-listp poly2) 
                (equal (len (double-rewrite poly1)) 
                       (len (double-rewrite poly2))) 
                (not (equal (+ (car (last (double-rewrite poly1))) 
                               (car (last (double-rewrite poly2)))) 
                            0))) 
           (dhnf-p (polynomial-+ poly1 poly2)))) 

(defthm 
  dhnf-p-polynomial-+-B 
  (implies (and (consp (double-rewrite poly2)) 
                (true-listp poly2) 
                (equal (len (double-rewrite poly1)) 
                       (len (double-rewrite poly2))) 
                (not (equal (+ (car (last (double-rewrite poly1))) 
                               (car (last (double-rewrite poly2)))) 
                            0))) 
           (dhnf-p (polynomial-+ poly1 poly2)))) 

(defthm 
  dhnf-p-polynomial-+-C 
  (implies (and (dhnf-p poly2) 
                (< (len (double-rewrite poly1)) 
                   (len (double-rewrite poly2)))) 
           (dhnf-p (polynomial-+ poly1 poly2)))) 

(defthm 
  dhnf-p-polynomial-+-D 
  (implies (and (dhnf-p poly1) 
                (< (len (double-rewrite poly2)) 
                   (len (double-rewrite poly1)))) 
           (dhnf-p (polynomial-+ poly1 poly2)))) 

(defthm 
  dhnf-p-polynomial-* 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2) 
                (consp (double-rewrite poly2))) 
           (dhnf-p (polynomial-* poly1 poly2)))) 
;; (polynomial-* (list 1) nil) => (0) 

(defthm 
  dhnf-p-add-const-polynomial 
  (implies (and (dhnf-p poly) 
                (consp (cdr (double-rewrite poly)))) 
           (dhnf-p (add-const-polynomial poly k)))) 

(defthm 
  dhnf-p-compose-polynomials-lemma 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2) 
                (consp (cdr poly1)) 
                (consp (cdr poly2))) 
           (dhnf-p (compose-polynomials poly1 poly2))) 
  :rule-classes nil) 

(defthm 
  dhnf-p-compose-polynomials 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2) 
                (consp (cdr (double-rewrite poly2)))) 
           (dhnf-p (compose-polynomials poly1 poly2))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION ADD-CONST-POLYNOMIAL) 
                               (:DEFINITION DHNF-P) 
                               (:DEFINITION POLYNOMIAL-*)) 
           :use dhnf-p-compose-polynomials-lemma))) 

(defthm 
  dhnf-p-compose-poly-with_-x 
  (implies (dhnf-p poly) 
           (dhnf-p (compose-poly-with_-x poly)))) 

(defthm 
  dhnf-p-compose-poly-with_x^2 
  (implies (dhnf-p poly) 
           (dhnf-p (compose-poly-with_x^2 poly)))) 

(defthm 
  scale-poly-by-nonNbr=scale-poly-by-0 
  (implies (not (acl2-numberp c)) 
           (equal (scale-polynomial poly c) 
                  (scale-polynomial poly 0)))) 

(defthm 
  compose-poly-with_x+d-when-nonNbr-d 
  (implies (not (acl2-numberp d)) 
           (equal (compose-poly-with_x+d poly d) 
                  (compose-poly-with_x+d poly 0)))) 

(defthm 
  dhnf-p-compose-poly-with_x+d-lemma 
  (implies (and (dhnf-p poly) 
                (acl2-numberp d)) 
           (dhnf-p (compose-poly-with_x+d poly d))) 
  :rule-classes nil) 

(defthm 
  dhnf-p-compose-poly-with_x+d 
  (implies (dhnf-p poly) 
           (dhnf-p (compose-poly-with_x+d poly d))) 
  :hints (("Goal" 
           :in-theory (disable compose-poly-with_x+d-when-nonNbr-d) 
           :use (dhnf-p-compose-poly-with_x+d-lemma 
                 compose-poly-with_x+d-when-nonNbr-d)))) 

(defthm 
  dhnf-p-divide-poly-by-x+a 
  (implies (dhnf-p poly) 
           (dhnf-p (divide-polynomial-with-remainder-by-x+a poly a)))) 

(defthm 
  dhnf-p-cdr-divide-poly-by-x+a 
  (implies (dhnf-p poly) 
           (dhnf-p (cdr (divide-polynomial-with-remainder-by-x+a poly a))))) 

(defthm 
  dhnf-p-divide-poly-by-list 
  (implies (dhnf-p poly) 
           (dhnf-p (divide-polynomial-by-list poly lst))))	

(defthm 
  dhnf-p-zero-poly=nil 
  (implies (and (dhnf-p poly) 
                (zero-polynomial-p poly)) 
           (equal (equal poly nil) t))) 

(defthm 
  truncate-poly=poly-when-dhnf-poly 
  (implies (dhnf-p poly) 
           (equal (truncate-polynomial poly) 
                  poly))) 

(defthm 
  truncate-poly=poly_=_dhnf-poly 
  (implies (acl2-number-listp poly) 
           (equal (equal (truncate-polynomial poly) 
                         poly) 
                  (dhnf-p poly)))) 
;;---------------------- 
(defun 
    DHscale-polynomial (poly c) 
  (if (and (acl2-numberp c) 
           (not (zerop c))) 
      (scale-polynomial poly c) 
    nil)) 

(defthm 
  dhnf-p-DHscale-polynomial 
  (implies (dhnf-p poly) 
           (dhnf-p (DHscale-polynomial poly c)))) 

(defthm 
  eval-DHscale-polynomial 
  (equal (eval-polynomial (DHscale-polynomial poly c) x) 
         (* c (eval-polynomial poly x)))) 

(defthm 
  DHscale-DHscale-polynomial 
  (equal (DHscale-polynomial (DHscale-polynomial poly c1) c2) 
         (DHscale-polynomial poly (* c1 c2)))) 
;;---------------------- 
(defun 
    DHpolynomial-+ (poly1 poly2) 
  (if (consp poly1) 
      (if (consp poly2) 
          (truncate-polynomial (polynomial-+ poly1 poly2)) 
        poly1) 
    poly2)) 

(defthm 
  dhnf-p-DHpolynomial-+ 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2)) 
           (dhnf-p (DHpolynomial-+ poly1 poly2)))) 

(defthm 
  eval-DHpolynomial-+ 
  (equal (eval-polynomial (DHpolynomial-+ poly1 poly2) x) 
         (+ (eval-polynomial poly1 x) 
            (eval-polynomial poly2 x)))) 

(defthmD 
  commutativity-of-DHpolynomial-+ 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2)) 
           (equal (DHpolynomial-+ poly1 poly2) 
                  (DHpolynomial-+ poly2 poly1))) 
  :hints (("Goal" 
           :in-theory (enable COMMUTATIVITY-OF-POLYNOMIAL-+)))) 
;;----------------------- 
(defun 
    DHpolynomial-* (poly1 poly2) 
  (if (consp poly2) 
      (polynomial-* poly1 poly2) 
    nil)) 

(defthm 
  dhnf-p-DHpolynomial-* 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2)) 
           (dhnf-p (DHpolynomial-* poly1 poly2)))) 

(defthm 
  eval-DHpolynomial-* 
  (equal (eval-polynomial (DHpolynomial-* poly1 poly2) x) 
         (* (eval-polynomial poly1 x) 
            (eval-polynomial poly2 x)))) 

(defthm 
  consp-DHpolnomial-* 
  (equal (consp (DHpolynomial-* poly1 poly2)) 
         (and (consp (double-rewrite poly1)) 
              (consp (double-rewrite poly2))))) 

(defthm 
  len-DHpolynomial-* 
  (equal (len (DHpolynomial-* poly1 poly2)) 
         (cond ((atom (double-rewrite poly1)) 
                0) 
               ((atom (double-rewrite poly2)) 
                0) 
               (t (+ -1 
                     (len (double-rewrite poly1)) 
                     (len (double-rewrite poly2))))))) 
;;--------------------- 
(defun 
    DHcompose-polynomials (poly1 poly2) 
  (if (consp (cdr poly2)) 
      (compose-polynomials poly1 poly2) 
    (truncate-polynomial (compose-polynomials poly1 poly2)))) 
;;(compose-polynomials (list 0 1) nil) => (0) 
;;(compose-polynomials (list -2 1)(list 2)) => (0) 

(defthm 
  dhnf-p-DHcompose-polynomials 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2)) 
           (dhnf-p (DHcompose-polynomials poly1 poly2)))) 

(defthm 
  eval-polynomial-DHcompose-polynomials 
  (equal (eval-polynomial (DHcompose-polynomials poly1 poly2) z) 
         (eval-polynomial poly1 (eval-polynomial poly2 z)))) 
;;--------------------- 
(defun 
    max-norm-1C-list (lst) 
  (if (consp lst) 
      (max (norm-1C (car lst)) 
           (max-norm-1C-list (cdr lst))) 
    0)) 
;;===================== 
;; (max-norm-1C-list '(-3/5 4/5 #C(3/5 -4/5))) => 7/5 
;;===================== 

;; Time: 2.23 seconds 
(defthm 
  norm-1C-member<=max-norm-1C-list 
  (implies (member-equal x (double-rewrite lst)) 
           (<= (norm-1C x)(max-norm-1C-list lst)))) 

(defthm 
  member-i<=max-norm-1C-list 
  (implies (and (member-equal i (double-rewrite lst)) 
                (integerp i) 
                (<= 0 i)) 
           (<= i (max-norm-1C-list lst))) 
  :hints (("Goal" 
           :in-theory (disable norm-1C-member<=max-norm-1C-list) 
           :use (:instance 
                 norm-1C-member<=max-norm-1C-list 
                 (x i))))) 

(defun 
    next-integer (x) 
  (1+ (floor1 x))) 
;;================== 
;; (next-integer (max-norm-1C-list '(-3/5 4/5 #C(3/5 -4/5)))) => 2 
;;================== 

(defthm 
  next-integer-<=-x+1 
  (implies (real/rationalp x) 
           (not (< (+ 1 x) (next-integer x)))) 
  :rule-classes (:linear :rewrite)) 

(defthm 
  x-<-next-integer 
  (implies (real/rationalp x) 
           (< x (next-integer x))) 
  :rule-classes (:linear :rewrite)) 

(defthm 
  next-integer-abs>0 
  (< 0 (next-integer (abs x))) 
  :rule-classes (:linear :rewrite) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION ABS))))) 

(defthm 
  next-integer-norm-1C>0 
  (< 0 (next-integer (norm-1C x))) 
  :rule-classes (:linear :rewrite)) 

(defthm 
  next-integer-max-norm-1C-list>0 
  (< 0 (next-integer (max-norm-1C-list lst))) 
  :rule-classes (:linear :rewrite)) 

(defthm 
  NOT-next-integer-max-norm-1C-list_member_lst 
  (not (member-equal (next-integer (max-norm-1C-list lst)) 
                     lst)) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION NEXT-INTEGER) 
                               (:DEFINITION NORM-1C) 
                               member-i<=max-norm-1C-list) 
           :use (:instance member-i<=max-norm-1C-list 
                           (i (next-integer (max-norm-1C-list lst))))))) 

(in-theory (disable (:definition next-integer))) 

(defthm 
  next-int-max-norm-list-find-zeros-NOTaZero 
  (implies (and (polynomial-p poly) 
                (not (zero-polynomial-p poly))) 
           (not (equal (eval-polynomial poly 
                                        (next-integer 
                                         (max-norm-1C-list 
                                          (find-distinct-zeros-of-poly poly)))) 
                       0))) 
  :hints (("Goal" 
           :in-theory (disable find-distinct-zeros-of-poly-contains-all-zeros) 
           :use (:instance 
                 find-distinct-zeros-of-poly-contains-all-zeros 
                 (x (next-integer (max-norm-1C-list (find-distinct-zeros-of-poly poly)))))))) 

(defthm 
  zero-poly=nil-for-dhnf 
  (implies (dhnf-p poly) 
           (equal (zero-polynomial-p poly) 
                  (equal poly nil)))) 

(defthm 
  eval-poly-next-int-max-norm-list=0_=_poly=nil 
  (implies (dhnf-p poly) 
           (equal (equal (eval-polynomial poly 
                                          (next-integer 
                                           (max-norm-1C-list 
                                            (find-distinct-zeros-of-poly poly)))) 
                         0) 
                  (equal poly nil)))) 

(defthm 
  members-of-zero-poly-are-0 
  (implies (and (zero-polynomial-p poly) 
                (member-equal x (double-rewrite poly))) 
           (equal (equal x 0) 
                  t))) 

(defthm 
  consp-truncate-poly 
  (implies (and (not (equal x 0)) 
                (member-equal x (double-rewrite poly))) 
           (consp (truncate-polynomial poly)))) 

(defthmD 
  list-equiv=equal 
  (implies (and (true-listp lst1) 
                (true-listp lst2)) 
           (equal (list-equiv lst1 lst2) 
                  (equal lst1 lst2))) 
  :hints (("Goal" 
           :in-theory (enable (:definition list-equiv))))) 

(defun 
    not-list-equiv-witness (lst1 lst2 i) 
  (cond ((consp lst1) 
         (cond ((atom lst2) 
                -1) 
               ((not (equal (car lst1)(car lst2))) 
                i) 
               (t (not-list-equiv-witness (cdr lst1)(cdr lst2)(+ 1 i))))) 
        ((consp lst2) 
         -2) 
        (t nil))) 
;; ========================================= 
;; (not-list-equiv-witness '(a b) 'a 0) => -1 
;; (not-list-equiv-witness 'b '(a b) 0) => -2 
;; (not-list-equiv-witness '(a b) '(a b) 0) => NIL 
;; (not-list-equiv-witness '(a b) '(b b) 0) => 0 
;; (not-list-equiv-witness '(a a) '(a b) 0) => 1 
;; ========================================== 

(defthmD 
  not-list-equiv-witness=-1 
  (implies (natp i) 
           (equal (equal -1 (not-list-equiv-witness lst1 lst2 i)) 
                  (and (< (len (double-rewrite lst2))(len (double-rewrite lst1))) 
                       (prefixp (double-rewrite lst2)(double-rewrite lst1)))))) 

(defthmD 
  not-list-equiv-witness=-2 
  (implies (natp i) 
           (equal (equal -2 (not-list-equiv-witness lst1 lst2 i)) 
                  (and (< (len (double-rewrite lst1))(len (double-rewrite lst2))) 
                       (prefixp (double-rewrite lst1)(double-rewrite lst2)))))) 

(defthmD 
  not-list-equiv-witness=nil 
  (implies (natp i) 
           (equal (null (not-list-equiv-witness lst1 lst2 i)) 
                  (list-equiv (double-rewrite lst1)(double-rewrite lst2))))) 

(defthm 
  not-list-equiv-witness<i+len-1 
  (implies (and (natp (not-list-equiv-witness lst1 lst2 i)) 
                (natp i)) 
           (< (not-list-equiv-witness lst1 lst2 i) 
              (+ i (len lst1))))) 

(defthm 
  not-list-equiv-witness<i+len-2 
  (implies (and (natp (not-list-equiv-witness lst1 lst2 i)) 
                (natp i)) 
           (< (not-list-equiv-witness lst1 lst2 i) 
              (+ i (len lst2))))) 

(defthm 
  not-list-equiv-witness>=i 
  (implies (and (natp (not-list-equiv-witness lst1 lst2 i)) 
                (natp i)) 
           (>= (not-list-equiv-witness lst1 lst2 i) 
               i)) 
  :rule-classes (:linear :rewrite)) 

(defthm 
  not-equal-nth-not-list-equiv-witness 
  (implies (and (natp (not-list-equiv-witness lst1 lst2 i)) 
                (natp i)) 
           (not (equal (nth (+ (- i)(not-list-equiv-witness lst1 lst2 i)) lst1) 
                       (nth (+ (- i)(not-list-equiv-witness lst1 lst2 i)) lst2))))) 

;; Example: This theorem proves without some recommended double-rewrite's. 
;; Next theorem fails to prove with the recommended double-rewrite's. 
;; So, use this theorem to prove next theorem 
;; (:INDUCTION NTH) used to modify the induction scheme used to prove this theorem 
(defthm 
  nth-poly-+-poly--_missing-2-double-rewrites 
  (implies (and (natp i) 
                (< i (len (double-rewrite lst1))) 
                (equal (len (double-rewrite lst1)) 
                       (len (double-rewrite lst2)))) 
           (equal (nth i (polynomial-+ lst1 
                                       (polynomial-- lst2))) 
                  (+ (nth i lst1) 
                     (- (nth i lst2))))) 
  :rule-classes nil) 

(defthm 
  nth-poly-+-poly-- 
  (implies (and (natp i) 
                (< i (len (double-rewrite lst1))) 
                (equal (len (double-rewrite lst1)) 
                       (len (double-rewrite lst2)))) 
           (equal (nth i (polynomial-+ lst1 
                                       (polynomial-- lst2))) 
                  (+ (nth i (double-rewrite lst1)) 
                     (- (nth i (double-rewrite lst2)))))) 
  :hints (("Goal" 
           :use nth-poly-+-poly--_missing-2-double-rewrites))) 

(defthm 
  acl2-numberp-nth 
  (implies (and (polynomial-p poly) 
                (natp i) 
                (< i (len poly))) 
           (acl2-numberp (nth i poly)))) 

(defthm 
  not-zerop-nth-not-list-equiv-witness 
  (implies (and (polynomial-p poly1) 
                (polynomial-p poly2) 
                (equal (len (double-rewrite poly1))(len (double-rewrite poly2))) 
                (natp (not-list-equiv-witness poly1 poly2 0))) 
           (not (zerop (nth (not-list-equiv-witness poly1 poly2 0) 
                            (polynomial-+ poly1 
                                          (polynomial-- poly2)))))) 
  :hints (("Goal" 
           :in-theory (disable not-equal-nth-not-list-equiv-witness 
                               nth-poly-+-poly-- 
                               acl2-numberp-nth) 
           :use ((:instance not-equal-nth-not-list-equiv-witness 
                            (lst1 poly1) 
                            (lst2 poly2) 
                            (i 0)) 
                 (:instance nth-poly-+-poly-- 
                            (lst1 poly1) 
                            (lst2 poly2) 
                            (i (not-list-equiv-witness poly1 poly2 0))) 
                 (:instance acl2-numberp-nth 
                            (poly poly1) 
                            (i (not-list-equiv-witness poly1 poly2 0))) 
                 (:instance acl2-numberp-nth 
                            (poly poly2) 
                            (i (not-list-equiv-witness poly1 poly2 0))))))) 

(defthm 
  not-list-equiv-witness<max 
  (implies (natp (not-list-equiv-witness lst1 lst2 0)) 
           (< (not-list-equiv-witness lst1 lst2 0) 
              (max (len lst1)(len lst2)))) 
  :hints (("Goal" 
           :in-theory (disable not-list-equiv-witness<i+len-1) 
           :use ((:instance not-list-equiv-witness<i+len-1 
                            (i 0)))))) 

(defthm 
  not-list-equiv-witness<len-poly-+-poly-- 
  (implies (natp (not-list-equiv-witness lst1 lst2 0)) 
           (< (not-list-equiv-witness lst1 lst2 0) 
              (len (polynomial-+ lst1 
                                 (polynomial-- lst2))))) 
  :hints (("Goal" 
           :in-theory (disable not-list-equiv-witness<max) 
           :use not-list-equiv-witness<max))) 

(defthm 
  member-equal-nth 
  (implies (and (natp i) 
                (< i (len lst))) 
           (member-equal (nth i lst) lst))) 

(defthm 
  member-equal-nth-not-list-equiv-witness 
  (implies (natp (not-list-equiv-witness lst1 lst2 0)) 
           (member-equal (nth (not-list-equiv-witness lst1 lst2 0) 
                              (polynomial-+ lst1 
                                            (polynomial-- lst2))) 
                         (polynomial-+ lst1 
                                       (polynomial-- lst2)))) 
  :hints (("Goal" 
           :in-theory (disable not-list-equiv-witness<len-poly-+-poly--) 
           :use not-list-equiv-witness<len-poly-+-poly--))) 

(defthm 
  consp-truncate-poly-+-poly-- 
  (implies (and (polynomial-p poly1) 
                (polynomial-p poly2) 
                (equal (len (double-rewrite poly1))(len (double-rewrite poly2))) 
                (natp (not-list-equiv-witness poly1 poly2 0))) 
           (consp (truncate-polynomial (polynomial-+ poly1 
                                                     (polynomial-- poly2))))) 
  :hints (("Goal" 
           :in-theory (disable not-zerop-nth-not-list-equiv-witness) 
           :use (not-zerop-nth-not-list-equiv-witness)))) 

(defthm 
  consp-DHpoly-+-poly--A 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2) 
                (< (len (double-rewrite poly1)) 
                   (len (double-rewrite poly2)))) 
           (consp (DHpolynomial-+ poly1 (polynomial-- poly2))))) 

(defthm 
  consp-DHpoly-+-poly--B 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2) 
                (< (len (double-rewrite poly2)) 
                   (len (double-rewrite poly1)))) 
           (consp (DHpolynomial-+ poly1 (polynomial-- poly2))))) 

(defthm 
  DHpoly-+-poly--_=_truncate-poly-+-poly-- 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2)) 
           (equal (DHpolynomial-+ poly1 
                                  (polynomial-- poly2)) 
                  (truncate-polynomial (polynomial-+ poly1 
                                                     (polynomial-- poly2)))))) 

(defthm 
  consp-DHpoly-+-poly--C 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2) 
                (equal (len (double-rewrite poly1)) 
                       (len (double-rewrite poly2))) 
                (natp (not-list-equiv-witness poly1 poly2 0))) 
           (consp (DHpolynomial-+ poly1 (polynomial-- poly2))))) 

(defthm 
  integerp-not-list-equiv-witness 
  (implies (and (natp i) 
                (not-list-equiv-witness lst1 lst2 i)) 
           (integerp (not-list-equiv-witness lst1 lst2 i)))) 

(defthm 
  natp-not-list-equiv-witness 
  (implies (and (natp i) 
                (not-list-equiv-witness lst1 lst2 i) 
                (equal (len (double-rewrite lst1)) 
                       (len (double-rewrite lst2)))) 
           (natp (not-list-equiv-witness lst1 lst2 i)))) 

(defthm 
  not-list-equiv=natp-not-list-equiv-witness 
  (implies (natp i) 
           (equal (not (list-equiv lst1 lst2)) 
                  (or (< (len lst1)(len lst2)) 
                      (< (len lst2)(len lst1)) 
                      (natp (not-list-equiv-witness lst1 lst2 i))))) 
  :rule-classes nil 
  :hints (("Goal" 
           :use NOT-LIST-EQUIV-WITNESS=NIL))) 

(defthm 
  consp-DHpoly-+-poly-- 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2) 
                (not (list-equiv (double-rewrite poly1) 
                                 (double-rewrite poly2)))) 
           (consp (DHpolynomial-+ poly1 (polynomial-- poly2)))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION DHPOLYNOMIAL-+) 
                               DHPOLY-+-POLY--_=_TRUNCATE-POLY-+-POLY--) 
           :cases ((< (len poly1)(len poly2)) 
                   (< (len poly2)(len poly1))) 
           :use (:instance not-list-equiv=natp-not-list-equiv-witness 
                           (lst1 poly1) 
                           (lst2 poly2) 
                           (i 0))))) 

(defthm 
  next-int-max-norm-list-find-zeros-NOTaZero-A 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2) 
                (not (list-equiv (double-rewrite poly1) 
                                 (double-rewrite poly2)))) 
           (not (equal (eval-polynomial (DHpolynomial-+ poly1 (polynomial-- poly2)) 
                                        (next-integer 
                                         (max-norm-1C-list 
                                          (find-distinct-zeros-of-poly 
                                           (DHpolynomial-+ poly1 
                                                           (polynomial-- poly2)))))) 
                       0))) 
  :hints (("Goal" 
           :in-theory (disable consp-DHpoly-+-poly-- 
                               DHPOLY-+-POLY--_=_TRUNCATE-POLY-+-POLY-- 
                               EVAL-DHPOLYNOMIAL-+ 
                               (:DEFINITION DHPOLYNOMIAL-+)) 
           :use consp-DHpoly-+-poly--))) 

(defthm 
  NOT-equal-eval-poly-next-int-max-norm-list-find-zeros 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2) 
                (not (list-equiv (double-rewrite poly1) 
                                 (double-rewrite poly2)))) 
           (not (equal (eval-polynomial poly1 
                                        (next-integer 
                                         (max-norm-1C-list 
                                          (find-distinct-zeros-of-poly 
                                           (DHpolynomial-+ poly1 
                                                           (polynomial-- poly2)))))) 
                       (eval-polynomial poly2 
                                        (next-integer 
                                         (max-norm-1C-list 
                                          (find-distinct-zeros-of-poly 
                                           (DHpolynomial-+ poly1 
                                                           (polynomial-- poly2))))))))) 
  :hints (("Goal" 
           :in-theory (disable next-int-max-norm-list-find-zeros-NOTaZero-A 
                               DHPOLY-+-POLY--_=_TRUNCATE-POLY-+-POLY-- 
                               (:DEFINITION DHPOLYNOMIAL-+)) 
           :use next-int-max-norm-list-find-zeros-NOTaZero-A))) 

(defthm 
  list-equiv-implies-equal-eval-polynomial-1 
  (implies (list-equiv lst1 lst2) 
           (equal (eval-polynomial lst1 x) 
                  (eval-polynomial lst2 x))) 
  :rule-classes :congruence 
  :hints (("Goal" 
           :in-theory (enable (:INDUCTION FAST-LIST-EQUIV)) 
           :induct (fast-list-equiv lst1 lst2)))) 

(defun 
    dhnf-p-list-equiv-witness (poly1 poly2) 
  (next-integer 
   (max-norm-1C-list 
    (find-distinct-zeros-of-poly 
     (DHpolynomial-+ poly1 
                     (polynomial-- poly2)))))) 

(defthm 
  posp-dhnf-p-list-equiv-witness 
  (posp (dhnf-p-list-equiv-witness poly1 poly2))) 

(defthm 
  NOT-equal-eval-poly-dhnf-p-list-equiv-witness 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2) 
                (not (list-equiv (double-rewrite poly1) 
                                 (double-rewrite poly2)))) 
           (not (equal (eval-polynomial poly1 
                                        (dhnf-p-list-equiv-witness poly1 poly2)) 
                       (eval-polynomial poly2 
                                        (dhnf-p-list-equiv-witness poly1 poly2))))) 
  :hints (("Goal" 
           :in-theory (disable NOT-equal-eval-poly-next-int-max-norm-list-find-zeros) 
           :use NOT-equal-eval-poly-next-int-max-norm-list-find-zeros))) 

(defthm 
  eval-poly-dhnf-p-list-equiv-witness 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2)) 
           (equal (equal (eval-polynomial poly1 
                                          (dhnf-p-list-equiv-witness poly1 poly2)) 
                         (eval-polynomial poly2 
                                          (dhnf-p-list-equiv-witness poly1 poly2))) 
                  (list-equiv poly1 poly2))) 
  :hints (("Goal" 
           :in-theory (disable (:definition dhnf-p-list-equiv-witness))))) 

(defthm 
  eval-poly-dhnf-p-list-equiv-witness-A 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2)) 
           (equal (equal (eval-polynomial poly1 
                                          (dhnf-p-list-equiv-witness poly1 poly2)) 
                         (eval-polynomial poly2 
                                          (dhnf-p-list-equiv-witness poly1 poly2))) 
                  (equal poly1 poly2))) 
  :hints (("Goal" 
           :in-theory (e/d (LIST-EQUIV=EQUAL) 
                           ((:definition dhnf-p-list-equiv-witness)))))) 

(defun-sk 
  forall-x-eval-poly=eval-poly (poly1 poly2) 
  (forall x (equal (eval-polynomial poly1 x) 
                   (eval-polynomial poly2 x))) 
  :rewrite :direct) 

(defthm 
  eval-poly-dhnf-p-list-equiv-witness-B 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2) 
                (equal (eval-polynomial (double-rewrite poly1) 
                                        (dhnf-p-list-equiv-witness poly1 poly2)) 
                       (eval-polynomial (double-rewrite poly2) 
                                        (dhnf-p-list-equiv-witness poly1 poly2)))) 
           (forall-x-eval-poly=eval-poly poly1 poly2)) 
  :hints (("Goal" 
           :in-theory (disable (:definition dhnf-p-list-equiv-witness))))) 

(defthm 
  eval-poly-dhnf-p-list-equiv-witness-C 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2)) 
           (equal (forall-x-eval-poly=eval-poly poly1 poly2) 
                  (equal (eval-polynomial (double-rewrite poly1) 
                                          (dhnf-p-list-equiv-witness poly1 poly2)) 
                         (eval-polynomial (double-rewrite poly2) 
                                          (dhnf-p-list-equiv-witness poly1 poly2))))) 
  :hints (("Goal" 
           :in-theory (disable (:definition dhnf-p-list-equiv-witness) 
                               (:DEFINITION FORALL-X-EVAL-POLY=EVAL-POLY) 
                               eval-poly-dhnf-p-list-equiv-witness 
                               eval-poly-dhnf-p-list-equiv-witness-A)))) 

(defthm 
  forall-x-eval-poly=eval-poly_=_equal 
  (implies (and (dhnf-p poly1) 
                (dhnf-p poly2)) 
           (equal (forall-x-eval-poly=eval-poly poly1 poly2) 
                  (equal poly1 poly2))) 
  :hints (("Goal" 
           :in-theory (disable (:definition dhnf-p-list-equiv-witness))))) 

(defthm 
  forall-x-eval-truncate-poly=eval-truncate-poly-+_forall-x-eval-poly=eval-poly 
  (implies (and (polynomial-p poly1) 
                (polynomial-p poly2)) 
           (equal (forall-x-eval-poly=eval-poly (truncate-polynomial poly1) 
                                                (truncate-polynomial poly2)) 
                  (forall-x-eval-poly=eval-poly poly1 poly2))) 
  :hints (("Goal" 
           :in-theory (disable forall-x-eval-poly=eval-poly_=_equal 
                               FORALL-X-EVAL-POLY=EVAL-POLY-NECC 
                               (:DEFINITION DHNF-P-LIST-EQUIV-WITNESS) 
                               EVAL-POLY-DHNF-P-LIST-EQUIV-WITNESS-C) 
           :use ((:instance FORALL-X-EVAL-POLY=EVAL-POLY-NECC 
                            (poly1 (truncate-polynomial poly1)) 
                            (poly2 (truncate-polynomial poly2)) 
                            (x (FORALL-X-EVAL-POLY=EVAL-POLY-WITNESS POLY1 POLY2))) 
                 (:instance FORALL-X-EVAL-POLY=EVAL-POLY-NECC 
                            (x (FORALL-X-EVAL-POLY=EVAL-POLY-WITNESS 
                                (truncate-polynomial POLY1) 
                                (truncate-polynomial POLY2)))))))) 

(defthm 
  forall-x-eval-poly=eval-poly_=_equal-truncate-poly 
  (implies (and (polynomial-p poly1) 
                (polynomial-p poly2)) 
           (equal (forall-x-eval-poly=eval-poly poly1 poly2) 
                  (equal (truncate-polynomial poly1) 
                         (truncate-polynomial poly2)))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION DHNF-P-LIST-EQUIV-WITNESS) 
                               (:DEFINITION FORALL-X-EVAL-POLY=EVAL-POLY) 
                               forall-x-eval-poly=eval-poly_=_equal) 
           :use (:instance forall-x-eval-poly=eval-poly_=_equal 
                           (poly1 (truncate-polynomial poly1)) 
                           (poly2 (truncate-polynomial poly2)))))) 
