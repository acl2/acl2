;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; John Cowles,
;; Knuth's Generalization of McCarthy's 91 Function.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Exercise 3.

;; This exercise is challenging.

;; Use ACL2 to formalize and verify an argument outlined in the
;; case study.  The argument is not repeated here.  Avoid using
;; DefAxiom when introducing the following equation into ACL2.
;; Instead use encapsulate to constrain M to satisfy the equation
;; for integers x.

;;   M(x) <==  if  x > 100  then   x - 10
;;                          else   M(M(x+11)).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Answer.
;; Submit the following to a newly started ACL2:

(in-package "ACL2") ; in order to certify this book
(include-book "../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

(encapsulate
 ;; Signature:
 ((M (x) t))
 ;;--------------------
 ;; Provide witness:
 (local (defun
	    M (x)
	    (if (> x 100)
		(- x 10)
	        91)))
 ;;---------------------
 ;; Consistent Axiom:
 (defthm
     McCarthy-91-Def
     (implies (integerp x)
	      (equal (M x)
		     (if (> x 100)
			 (- x 10)
		         (M (M (+ x 11))))))
     :rule-classes nil)
  ) ;; end encapsulate

(defthm
    M-for-x>100
    (implies (and (integerp x)
		  (> x 100))
	     (equal (M x)(- x 10)))
    :hints (("Goal"
	     :use McCarthy-91-Def)))

(defthm
    M-for-x<=100
    (implies (and (integerp x)
		  (<= x 100))
	     (equal (M x)(M (M (+ 11 x)))))
    :hints (("Goal"
	     :use McCarthy-91-Def)))

(defthm
    M-at_11+x_for-x>=90
    (implies (and (integerp x)
		  (<= 90 x)
		  (<= x 100))
	     (equal (M (+ 11 x)) (+ x 1))))

(defthm
    M-for-x>=90
    (implies (and (integerp x)
		  (<= 90 x)
		  (<= x 100))
	     (equal (M (+ 1 x))
		    (M x))))

(defun
    measure (x)
    ;; Note use of ifix.
    (let ((x (ifix x)))
         (if (> x 100)
	     0
	     (- 101 x))))

(defthm fact-1
 (e0-ordinalp (measure x))
 :rule-classes nil)

(defthm fact-2
 (implies (and (integerp x)
	       (<= x 100))
	  (e0-ord-< (measure (+ x 11))
		    (measure x)))
 :rule-classes nil)

(defun
    Induct-Hint-1 (x)
    (declare (xargs :measure (measure x)))
    (let ((x (ifix x)))
         (if (> x 100)
	     t
	     (Induct-Hint-1 (+ x 1)))))

(defthm
    Type-of-M-for-x>=90
    (implies (and (integerp x)
		  (>= x 90))
	     (and (integerp (M x))
		  (> (M x) 90)))
    :hints (("Goal"
	     :in-theory (disable M-for-x<=100)
	     :induct (Induct-Hint-1 x))))

(defun
    Induct-Hint-2 (x)
    (declare (xargs :measure (measure x)))
    (let ((x (ifix x)))
         (if (>= x 90)
	     t
	     (Induct-Hint-2 (+ x 11)))))

(defthm
    Type-of-M
    (implies (integerp x)
	     (and (integerp (M x))
		  (> (M x) 90)))
    :hints (("Goal"
	     :in-theory (disable M-for-x>=90)
	     :induct (Induct-Hint-2 x)))
    :rule-classes ((:type-prescription
		    :corollary
		    (implies (integerp x)
			     (integerp (M x))))
		   (:linear
		    :corollary
		    (implies (integerp x)
			     (> (M x) 90)))))

(defthm fact-3
 (implies (and (integerp x)
	       (<= x 100))
	  (e0-ord-< (measure (M (+ x 11)))
		    (measure x)))
 :hints (("Goal"
	  :in-theory (disable M-for-x<=100)
	  :cases ((< x 90)))))
