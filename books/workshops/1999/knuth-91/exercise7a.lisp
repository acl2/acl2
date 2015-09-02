;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; John Cowles,
;; Knuth's Generalization of McCarthy's 91 Function.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Exercise 7.

;; This exercise shows that the existence of an unique total
;; function, satisfying a given recursive equation, is not enough
;; to guarantee termination of the recursion in Common Lisp and
;; ACL2.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part A.

;; Use encapsulate to verify, in ACL2, that the Common Lisp
;; function, identity, is the unique total function satisfying
;; the equation

;;        f(x)  =  if   f(x)  then  x
;;                            else  x.

;; Make sure this equation is not added as a :rewrite rule.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Answer.
;; Submit the following to a newly started ACL2:

(in-package "ACL2") ; in order to certify this book

(encapsulate
 ;; Signature:
 ((f (x) t))
 ;;----------------
 ;; Provide witness:
 (local
  (defun
      f (x)
      (identity x)))
 ;;------------------
 ;; Consistent Axiom:
 (defthm
     Non-halting-eqn
     (equal (f x)
	    (if (f x)
		x
	        x))
     :rule-classes nil)
 ) ;; end encapsulate

(defthm
    f-is-identity
    (equal (f x)
	   (identity x))
    :hints (("Goal"
	     :use non-halting-eqn)))
