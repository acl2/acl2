;;=============floor1-non-R.lisp============= 
;; ACL2 book for 
;; the function FLOOR1. 

;; FLOOR1 is built into ACL2(r), but not into ACL2. 

;; 12 FEB 2019 

(in-package "ACL2") 

#|============================ 
To certify: 
(certify-book "floor1-non-R" 
0 ;; world with no commands 
) 
=============================== 
To use: 
(include-book "floor1-non-R" 
:uncertified-okp nil 
:defaxioms-okp nil 
:skip-proofs-okp nil 
) 
================================ 
(LD "floor1-non-R.lisp") ; read and evaluate each form in file 
=============================== 
:set-gag-mode t ; enable gag-mode, suppressing most proof commentary 
(set-gag-mode t) ; same as above 
:set-gag-mode :goals ; same as above, but print names of goals when produced 
:set-gag-mode nil ; disable gag-mode 
================================ 
ACL2 Version 8.1 built February 11, 2019 15:37:06. 
System books directory "/home/acl2/acl2-8.1/acl2-8.1/books/". 
================================|# 

(local 
 (include-book "arithmetic-5/top" 
               :dir :system 
               :uncertified-okp nil 
               :defaxioms-okp nil 
               :skip-proofs-okp nil)) 

#-:non-standard-analysis
(defun 
    floor1 (x) 
  (floor x 1)) 

(DEFTHM 
  DEFAULT-FLOOR1 
  (IMPLIES (NOT (REAL/RATIONALP X)) 
           (EQUAL (FLOOR1 X) 0))) 

(DEFTHM 
  FLOOR1-INTEGER-X 
  (IMPLIES (INTEGERP X) 
           (EQUAL (FLOOR1 X) X))) 

(DEFTHM 
  FLOOR1-X-<=-X 
  (IMPLIES (REAL/RATIONALP X) 
           (<= (FLOOR1 X) X)) 
  :RULE-CLASSES :LINEAR) 

(DEFTHM 
  X-<-ADD1-FLOOR1-X 
  (IMPLIES (REAL/RATIONALP X) 
           (< X (1+ (FLOOR1 X)))) 
  :RULE-CLASSES :LINEAR) 

(defthm 
  floor1-abs>=0 
  (<= 0 (floor1 (abs x))) 
  :rule-classes :linear) 

(IN-THEORY (DISABLE (:DEFINITION FLOOR1))) 
