;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; John Cowles,
;; Knuth's Generalization of McCarthy's 91 Function.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Exercise 6.
;; Part A.

;; Use encapsulate to introduce and constrain ACL2 versions of
;; constants a, b, e, n so that e is a rational with e <= 0. Use
;; the ACL2 versions of a, b, n to formally state and admit the
;; definition,

;; K(x)  <==  if  x > a  then  x - b
;;                       else  n,

;; in ACL2. Next state and formally prove, in ACL2, the recursive
;; equation

;; K(x)  =  if  x > a  then  x - b
;;                     else  K(x + e).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Answer.
;; Submit the following to a newly started ACL2:

(in-package "ACL2") ; in order to certify this book

(encapsulate
 ;; Signatures:
 ((a () t)
  (b () t)
  (e () t)
  (n () t))
 ;;----------------
 ;; Provide witnesses:
 (local
  (defun
      a ()
      0))

 (local
  (defun
      b ()
      0))

 (local
  (defun
      e ()
      0))

 (local
  (defun
      n ()
      0))
 ;;------------------
 ;; Consistent Axiom:
 (defthm
     Type-of-e
     (and (rationalp (e))
	  (<= (e) 0))
     :rule-classes :type-prescription)
 ) ;; end encapsulate

(defun
    K (x)
    (if (> x (a))
	(- x (b))
        (n)))

(defthm fact-1
 (equal (K x)
	(if (> x (a))
	    (- x (b))
	  (K (+ x (e))))))

