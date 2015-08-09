;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; John Cowles,
;; Knuth's Generalization of McCarthy's 91 Function.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Exercise 1.

;; Use DefStub to tell ACL2 about a new function f.  Next, use
;; DefAxiom to force ACL2 to add the equation:

;;               f(x) = if  x = 0  then  0
;;                                 else  f(x) + 1.

;; Make sure the equation is not added as a :rewrite rule.
;; Finally, use ACL2 to verify that nil is, indeed, a theorem of
;; this new theory.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Answer.
;; Submit the following to a newly started ACL2:

(in-package "ACL2") ; in order to certify this book

(defstub
    f (x) t)

(defaxiom
    Bad-equation
    (equal (f x)
	   (if (equal x 0)
	       0
	       (+ (f x) 1)))
    :rule-classes nil)

(defthm bad-consequence
 ;; Bad-equation renders ACL2 unsound!
 nil
 :rule-classes nil
 :hints (("Goal"
	  :use (:instance
		Bad-equation
		(x 1)))))
