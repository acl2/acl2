;;=============floor1-non-R.lisp============= 
;; ACL2 book for 
;; the function FLOOR1. 

;; FLOOR1 is built into ACL2(r), but not into ACL2. 

;; 12 FEB 2019 

(in-package "ACL2") 

; cert_param: (uses-acl2r)

(local 
 (include-book "arithmetic-5/top" :dir :system 
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
