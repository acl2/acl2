;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; John Cowles,
;; Knuth's Generalization of McCarthy's 91 Function.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Exercise 4.

;; The trichotomy axiom says that exactly one of the relations,
;; X <_a Y, X = Y, Y <_a X is true. It naively translates into the
;; conjunction of the following:

;;  1. At least one of the relations is true
;;       X <_a Y  or  X = Y  or  Y <_a X;

;;  2. At most one of the relations is true
;;     (a) if  X <_a Y, then  (not (X = Y));
;;     (b) if  X <_a Y, then  (not (Y <_a X));
;;     (c) if  X = Y, then  (not (X <_a Y))  and  (not (Y <_a X));
;;     (d) if  Y <_a X, then  (not (X = Y))  and  (not (X <_a Y)).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part A.

;; Use DefStub to introduce a new function for <_a and use DefMacro
;; to introduce notation for X <=_a Y, which is used to abbreviate
;; (not (Y <_a X)).  State and prove, in ACL2, the equivalences:

;; (i)  Formula 1 is equivalent to the antisymmetry constraint:

;;        if  X <=_a Y  and  Y <=_a X, then  X = Y.

;; (ii) Formula 2b is equivalent to the asymmetry constraint:

;;        if  X <_a Y, then  X <=_a Y.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Answer.
;; Submit the following to a newly started ACL2:

(in-package "ACL2") ; in order to certify this book

(defstub
    <_a (x y)
    t)

(defmacro
   <=_a (x y)
   (list 'not (list '<_a y x)))
;;---------------------------------------
;;;;Part A(i)

(defthm fact-1
 (iff (or (<_a x y)
	  (equal x y)
	  (<_a y x))
      (implies (and (<=_a x y)
		    (<=_a y x))
	       (equal x y)))
 :rule-classes nil)
;;---------------------------------------
;;;;Part A(ii)

(defthm fact-2
 (iff (implies (<_a x y)
	       (not (<_a y x)))
      (implies (<_a x y)
	       (<=_a x y)))
 :rule-classes nil)
