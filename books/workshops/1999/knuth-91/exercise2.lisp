;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; John Cowles,
;; Knuth's Generalization of McCarthy's 91 Function.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Exercise 2.
;; Part A.

;; Formally state McCarthy's definition for the 91 function in
;; ACL2:

;;   M(x) <==  if  x > 100  then   x - 10
;;                          else   M(M(x+11)).

;; Use the following proposed measure:

;;   measure(x) <==  if   x > 100  then  0
;;                                 else  101 - x.

;; Observe ACL2's resistance to accepting this definition.
;; Carefully note the non-trivial part of the measure conjecture.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Answer.
;; Submit the following to a newly started ACL2:

(in-package "ACL2") ; in order to certify this book

(defun
    measure (x)
    (if (> x 100)
	0
        (- 101 x)))

#|
(defun
    M (x)
    ;; Fails -- Study the measure conjecture.
    (declare (xargs :measure (measure x)))
    (if (> x 100)
	(- x 10)
        (M (M (+ x 11)))))
|#

;;Some output from ACL2:

;; The non-trivial part of the measure conjecture is

;; Goal
;; (AND (E0-ORDINALP (MEASURE X))
;;      (IMPLIES (<= X 100)
;;               (E0-ORD-< (MEASURE (+ X 11))
;;                         (MEASURE X)))
;;      (IMPLIES (<= X 100)
;;               (E0-ORD-< (MEASURE (M (+ X 11)))
;;                         (MEASURE X)))).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Exercise 2.
;; Part B.

;; Formally state the following definition in ACL2:

;;  M(x) <==  if   x > 100  then  x - 10
;;                          else  91.

;; Observe that ACL2 accepts this definition. Next, formally state
;; and prove, in ACL2, that the next equation holds for all
;; integers x.

;;   M(x)  =  if  x > 100  then  x - 10
;;                         else  M(M(x+11)).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Answer.
;; Submit the following to a newly started ACL2:

(defun
    M (x)
    ;; Equation 1.3
    (if (> x 100)
	(- x 10)
        91))

(defthm
    Equation-1.4
    (implies (integerp x)
	     (equal (M x)
		    (if (> x 100)
			(- x 10)
		        (M (M (+ x 11)))))))
