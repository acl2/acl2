;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; John Cowles,
;; Knuth's Generalization of McCarthy's 91 Function.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Exercise 7.
;; (See also Part A.)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part B.

;; Use encapsulate to verify, in ACL2, that the function with two
;; inputs that always returns the constant 0 is the unique total
;; function satisfying the equation

;;       g(x,y)  =  if  zp(x)  then  0
;;                             else  g(x-1,g(x,y)).

;; Recall that zp is one of ACL2's idioms for testing whether its
;; input is 0.
;; Make sure this equation is not added as a :rewrite rule.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Answer.
;; Submit the following to a newly started ACL2:

;;This proof is inspired by a similar proof given by J Moore.

(in-package "ACL2") ; in order to certify this book

(encapsulate
 ;; Signature:
 ((g (x y) t))
 ;;----------------
 ;; Provide witness:
 (local
  (defun
      g (x y)
      (declare (ignore x y))
      0))
 ;;------------------
 ;; Consistent Axiom:
 (defthm
     Non-halting-eqn
     (equal (g x y)
	    (if (zp x)
		0
	        (g (- x 1) (g x y))))
     :rule-classes nil)
 ;; The recursion suggested by this equation does not halt in ACL2
 ;; and Common Lisp because of the innermost-first order of
 ;; evaluation. That is, the innermost call to g in the subterm
 ;; (g x y) is evaluated before the outermost call to g in
 ;; (g (- x 1) (g x y)) is evaluated.  The recursion halts in a
 ;; language that evaluates the outermost call first.
 ) ;; end encapsulate

(defthm
    G-at-zp
    (implies (zp x)
	     (equal (g x y) 0))
    :hints (("Goal"
	     :use Non-halting-eqn)))

(defthm
    G-not-at-zp
    (implies (not (zp x))
	     (equal (g (- x 1) (g x y))
		    (g x y)))
    :hints (("Goal"
	     :use Non-halting-eqn)))

(defun
    Induct-hint (x y)
    (if (zp x)
	y
        (Induct-hint (- x 1)(g x y))))

(defthm
    G-is-zero
    (equal (g x y) 0)
    :hints (("Goal"
	     :induct (induct-hint x y))))
