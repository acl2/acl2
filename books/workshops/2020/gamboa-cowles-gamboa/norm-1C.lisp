;;===========norm-1C.lisp================= 
;; ACL2 & ACL2(r) book for 
;; norm-1C(a+bi) = |a|+|b| [Manhattan norm] 

;; 15 FEB 2019 

(in-package "ACL2") 
#|================================ 
norm-1C is a norm on the set of acl2-numberps. 

Axioms for a norm: 
For acl2-numberps x & y, 
norm(x) >= 0 

norm(x) = 0 iff x = 0 

For realp a, 
norm(a*x) = abs(a)*norm(x) 

norm(x+y) <= norm(x) + norm(y) [triangle inequality] 
----------------------------- 
In addition, norm-1C satisfies 

norm-1C(x*y) <= norm-1C(x)*norm-1C(y) 

For real/rationalp x, 
norm-1C(x) = abs(x) 

norm-1C(- x) = norm-1C(x) 

norm-1C(x) - norm-1C(y) <= norm-1C(x+y) 

norm-1C(x) - norm-1C(y) <= norm-1C(x-y) 

For i>=0, 
norm-1C(expt(x i)) <= expt(norm-1C(x) i) 
-------------------------------- 
For ACL2(r) 

i-small(norm-1C(x)) = i-small(x) 

i-large(norm-1C(x)) = i-large(x) 

For i-limited x, 
standard-part(norm-1C(x)) = norm-1C(standard-part(x)) 
=================================|# 
#|==================================== 
To certify: 
(certify-book "norm-1C" 
0 ;; world with no commands 
) 
=============================== 
To use: 
(include-book "norm-1C" 
:uncertified-okp nil 
:defaxioms-okp nil 
:skip-proofs-okp nil 
) 
============================== 
(LD "norm-1C.lisp") ; read and evaluate each form in file 
======================================== 
:set-gag-mode t ; enable gag-mode, suppressing most proof commentary 
(set-gag-mode t) ; same as above 
:set-gag-mode :goals ; same as above, but print names of goals when produced 
:set-gag-mode nil ; disable gag-mode 
=================================== 
ACL2 Version 8.1 built February 11, 2019 15:37:06. 
System books directory "/home/acl2/acl2-8.1/acl2-8.1/books/". 
------------------------------------------------- 
ACL2 Version 8.1(r) built September 21, 2018 08:17:49. 
System books directory "/home/acl2/acl2-8.1r/acl2-8.1/books/". 
=================================|# 

(local 
 (include-book "arithmetic/top-with-meta" 
               :dir :system 
               :uncertified-okp nil 
               :defaxioms-okp nil 
               :skip-proofs-okp nil)) 

#+:non-standard-analysis 
(include-book "nonstd/nsa/nsa" 
              :dir :system 
              :uncertified-okp nil 
              :defaxioms-okp nil 
              :skip-proofs-okp nil) 

;;================================= 
;; abs is a norm for real/rationalp 
(defthm 
  real/rationalp-abs 
  (implies (real/rationalp x) 
           (real/rationalp (abs x))) 
  :rule-classes :type-prescription) 

(defthm 
  0<=abs 
  (<= 0 (abs x)) 
  :rule-classes :linear) 

(defthm 
  abs_x=0_=_x=0 
  (equal (equal (abs x) 0) 
         (equal x 0))) 

(defthm 
  abs_*=*_abs 
  (implies (and (real/rationalp a) 
                (real/rationalp x)) 
           (equal (abs (* a x)) 
                  (* (abs a)(abs x))))) 

(defthm 
  abs-triangle-inequality 
  (<= (abs (+ x y)) 
      (+ (abs x)(abs y)))) 

;;--------------------- 
(defthm 
  abs-triangle-inequality-1 
  (<= (+ (abs x)(- (abs y))) 
      (abs (+ x y)))) 

(defthm 
  abs-triangle-inequality-2 
  (<= (+ (abs x)(- (abs y))) 
      (abs (+ x (- y))))) 

;;====================== 
;; For ACL2(r) 
#+:non-standard-analysis 
(encapsulate 
  () 

  (defthm 
    small-abs 
    (equal (i-small (abs x)) 
           (i-small x))) 

  (defthm 
    large-abs 
    (equal (i-large (abs x)) 
           (i-large x))) 

  (defthm 
    standard-part-abs 
    (implies (and (realp x) 
                  (not (i-large x))) 
             (equal (standard-part (abs x)) 
                    (abs (standard-part x))))) 
  ) ;;end encapsulate 

;;================= 
;; norm-1C is a norm for acl2-numberp 
(defun 
    norm-1C (x) 
  (+ (abs (realpart x)) 
     (abs (imagpart x)))) 

(defthm 
  norm-1C-type-prescription 
  (and (real/rationalp (norm-1C x)) 
       (<= 0 (norm-1C x))) 
  :rule-classes nil) 

(defthm 
  norm-1C_x=0_=_x=0 
  (implies (acl2-numberp x) 
           (equal (equal (norm-1C x) 0) 
                  (equal x 0)))) 

;;---------------------- 
;;Three Useful Lemmas: 
(defthm 
  mult-def-complex 
  (equal (* x y) 
         (complex (- (* (realpart x) 
                        (realpart y)) 
                     (* (imagpart x) 
                        (imagpart y))) 
                  (+ (* (realpart x) 
                        (imagpart y)) 
                     (* (imagpart x) 
                        (realpart y))))) 
  :rule-classes nil 
  :hints (("Goal" 
           :use ((:instance 
                  COMPLEX-DEFINITION 
                  (x (realpart x)) 
                  (y (imagpart x))) 
                 (:instance 
                  COMPLEX-DEFINITION 
                  (x (realpart y)) 
                  (y (imagpart y))) 
                 (:instance 
                  COMPLEX-DEFINITION 
                  (x (- (* (realpart x) 
                           (realpart y)) 
                        (* (imagpart x) 
                           (imagpart y)))) 
                  (y (+ (* (realpart x) 
                           (imagpart y)) 
                        (* (imagpart x) 
                           (realpart y))))))))) 

(defthm 
  realpart-* 
  (equal (realpart (* x y)) 
         (- (* (realpart x) 
               (realpart y)) 
            (* (imagpart x) 
               (imagpart y)))) 
  :hints (("Goal" 
           :use mult-def-complex))) 

(defthm 
  imagpart-* 
  (equal (imagpart (* x y)) 
         (+ (* (realpart x) 
               (imagpart y)) 
            (* (imagpart x) 
               (realpart y)))) 
  :hints (("Goal" 
           :use mult-def-complex))) 
;;------------------------------------------- 

(defthm 
  norm-1C_*=*_abs-norm-1C 
  (implies (real/rationalp a) 
           (equal (norm-1C (* a x)) 
                  (* (abs a)(norm-1C x))))) 

(defthm 
  norm-1C-triangle-inequality 
  (<= (norm-1C (+ x y)) 
      (+ (norm-1C x)(norm-1C y)))) 

;;--------------------- 

(defthm 
  norm-1C-*_<=_*-norm-1C 
  (<= (norm-1C (* x y)) 
      (* (norm-1C x)(norm-1C y)))) 

(defthm 
  norm-1C=abs 
  (implies (real/rationalp x) 
           (equal (norm-1C x)(abs x)))) 

;;---------------------- 
;;Three More Useful Lemmas: 

(defthm 
  minus-def-complex 
  (equal (- x) 
         (complex (- (realpart x)) 
                  (- (imagpart x)))) 
  :rule-classes nil 
  :hints (("Goal" 
           :use ((:instance 
                  COMPLEX-DEFINITION 
                  (x (realpart x)) 
                  (y (imagpart x))) 
                 (:instance 
                  COMPLEX-DEFINITION 
                  (x (- (realpart x))) 
                  (y (- (imagpart x)))))))) 

(defthm 
  realpart-minus 
  (equal (realpart (- x)) 
         (- (realpart x))) 
  :hints (("Goal" 
           :use minus-def-complex))) 

(defthm 
  imagpart-minus 
  (equal (imagpart (- x)) 
         (- (imagpart x))) 
  :hints (("Goal" 
           :use minus-def-complex))) 
;;----------------------- 

(defthm 
  norm-1C_-=norm-1C 
  (equal (norm-1C (- x))(norm-1C x))) 

(defthm 
  norm-1C-triangle-inequality-1 
  (<= (+ (norm-1C x)(- (norm-1C y))) 
      (norm-1C (+ x y)))) 

(defthm 
  norm-1C-triangle-inequality-2 
  (implies (acl2-numberp x) 
           (<= (+ (norm-1C x)(- (norm-1C y))) 
               (norm-1C (+ x (- y))))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION norm-1C) 
                               norm-1C-triangle-inequality) 
           :use (:instance 
                 norm-1C-triangle-inequality 
                 (x (+ x (- y))))))) 

(defthmD 
  Norm-1C-expt<=expt-norm-1C-lemma-a 
  (IMPLIES (AND (<= (NORM-1C (* X (EXPT X (+ -1 I)))) 
                    (* (NORM-1C X) 
                       (NORM-1C (EXPT X (+ -1 I))))) 
                (<= (NORM-1C (EXPT X (+ -1 I))) 
                    (EXPT (NORM-1C X) (+ -1 I)))) 
           (<= (NORM-1C (* X (EXPT X (+ -1 I)))) 
               (* (NORM-1C X) 
                  (EXPT (NORM-1C X) (+ -1 I))))) 
  :hints (("Goal" 
           :in-theory (disable (:DEFINITION NORM-1C) 
                               norm-1C-*_<=_*-norm-1C 
                               *-PRESERVES->=-FOR-NONNEGATIVES 
                               <-*-LEFT-CANCEL) 
           :use (:instance 
                 (:theorem 
                  (implies (and (real/rationalp c) 
                                (<= 0 c) 
                                (real/rationalp d) 
                                (real/rationalp e) 
                                (<= d e)) 
                           (<= (* c d)(* c e)))) 
                 (c (NORM-1C X)) 
                 (d (NORM-1C (EXPT X (+ -1 I)))) 
                 (e (EXPT (NORM-1C X) (+ -1 I))))) 
          ("Subgoal 1" 
           :in-theory (enable <-*-LEFT-CANCEL)))) 

(defthm 
  Norm-1C-expt<=expt-norm-1C 
  (implies (<= 0 i) 
           (<= (Norm-1C (expt x i)) 
               (expt (norm-1C x) i))) 
  :hints (("Goal" 
           :in-theory (e/d (Norm-1C-expt<=expt-norm-1C-lemma-a) 
                           ((:DEFINITION NORM-1C)))))) 

(defthm 
  realpart-imagpart-<=-norm-1C 
  (and (<= (realpart x)(norm-1C x)) 
       (<= (imagpart x)(norm-1C x)))) 

(defthm 
  abs-realpart-imagpart-<=-norm-1c 
  (and (<= (abs (realpart x))(norm-1c x)) 
       (<= (abs (imagpart x))(norm-1c x)))) 

;;====================== 
;; For ACL2(r) 
#+:non-standard-analysis 
(encapsulate 
  () 

  (local 
   (defthm 
     small-norm-1C-lemma-a 
     (iff (i-small (norm-1C x)) 
          (and (i-small (realpart x)) 
               (i-small (imagpart x)))) 
     :rule-classes nil)) 

  (defthmD 
    small-norm-1C-lemma-b 
    (equal (i-small (norm-1C x)) 
           (and (i-small (realpart x)) 
                (i-small (imagpart x)))) 
    :hints (("Goal" 
             :use small-norm-1C-lemma-a))) 

  (defthm 
    small-norm-1C-lemma-c 
    (implies (acl2-numberp x) 
             (equal (i-small x) 
                    (and (i-small (realpart x)) 
                         (i-small (imagpart x))))) 
    :rule-classes nil 
    :hints (("Goal" 
             :in-theory (disable complex-small) 
             :use complex-small))) 

  (defthm 
    small-norm-1C 
    (implies (acl2-numberp x) 
             (equal (i-small (norm-1C x)) 
                    (i-small x))) 
    :hints (("Goal" 
             :in-theory (e/d (small-norm-1C-lemma-b) 
                             ((:definition norm-1C))) 
             :use small-norm-1C-lemma-c))) 

  (defthmD 
    limited-norm-1C-lemma 
    (equal (i-limited (norm-1C x)) 
           (and (i-limited (realpart x)) 
                (i-limited (imagpart x))))) 

  (defthmD 
    large-norm-1C-lemma 
    (implies (acl2-numberp x) 
             (equal (i-large x) 
                    (or (i-large (realpart x)) 
                        (i-large (imagpart x))))) 
    :hints (("Goal" 
             :in-theory (disable complex-large-1) 
             :use (complex-large-1 
                   complex-large-2)))) 

  (defthm 
    large-norm-1C 
    (implies (acl2-numberp x) 
             (equal (i-large (norm-1C x)) 
                    (i-large x))) 
    :hints (("Goal" 
             :use (limited-norm-1C-lemma 
                   large-norm-1C-lemma)))) 

  (defthm 
    standard-part-norm-1C 
    (implies (i-limited x) 
             (equal (standard-part (norm-1C x)) 
                    (norm-1C (standard-part x)))) 
    :hints (("Goal" 
             :in-theory (disable (:definition abs)) 
             :use large-norm-1C-lemma))) 
  ) ;; end encapsulate 
