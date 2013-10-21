;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; John Cowles,
;; Knuth's Generalization of McCarthy's 91 Function.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Exercise 4.
;; (See also Part A.)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part B.

;; Clearly there is some redundancy in the formulas of 2.  Use ACL2
;; to show that all the other formulas in 2 follow from 2b. Use
;; encapsulate to introduce <_a and state 2b.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Answer.
;; Submit the following to a newly started ACL2:

(in-package "ACL2") ; in order to certify this book

(encapsulate
 ;; Signature:
 ((<_a (x y) t))
 ;;----------------
 ;; Provide witness:
 (local (defun
	    <_a (x y)
	    (< x y)))
 ;;------------------
 ;; Consistent Axiom:
 (defthm
     Two-b
     (implies (<_a x y)
	      (not (<_a y x))))
 ) ; end encapsulate

(defthm
    Irreflexivity-of-<_a
    (not (<_a x x))
    :hints (("Goal"
	     :use (:instance
		   Two-b
		   (y x)))))

(defthm
    Two-a
    (implies (<_a x y)
	     (not (equal x y))))

(defthm
    Two-c
    (implies (equal x y)
	     (and (not (<_a x y))
		  (not (<_a y x)))))

(defthm
    Two-d
    (implies (<_a y x)
	     (and (not (<_a x y))
		  (not (equal x y)))))
