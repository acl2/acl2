;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; John Cowles,
;; Knuth's Generalization of McCarthy's 91 Function.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Exercise 6.
;; Part B.

;; Use encapsulate to introduce and constrain ACL2 versions of
;; constants a, b, e so that a and e are integers with e > 0. Use
;; these constants to formally state and admit the following
;; definition, intended for integer inputs x, in ACL2.

;; K(x)  <==  if  x > a  then  x - b
;;                       else  K(x + e).

;; Use the following measure:

;; measure(x)  <==  if  x > a  then  0
;;                             else  a + 1 - x.

;; Since the inputs to both K and the measure are intended to be
;; integers, non-integer inputs may be coerced to be integers by
;; the ACL2 function ifix.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Answer.
;; Submit the following to a newly started ACL2:

(in-package "ACL2") ; in order to certify this book

(encapsulate
 ;; Signatures:
 ((a () t)
  (b () t)
  (e () t))
 ;;----------------
 ;; Provide witnesses:
 (local
  (defun
      a ()
      1))

 (local
  (defun
      b ()
      1))

 (local
  (defun
      e ()
      1))
 ;;------------------
 ;; Consistent Axioms:
 (defthm
     Type-of-a
     (integerp (a))
     :rule-classes :type-prescription)

 (defthm
     Type-of-e
     (and (integerp (e))
	  (> (e) 0))
     :rule-classes :type-prescription)
 ) ;; end encapsulate

(defun
    measure (x)
    (let ((x (ifix x)))
	 (if (> x (a))
	     0
	     (- (+ (a) 1) x))))

(defun
    K (x)
    (declare (xargs :measure (measure x)))
    (let ((x (ifix x)))
         (if (> x (a))
	     (- x (b))
	     (K (+ x (e))))))
