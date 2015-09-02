;------------------------------------------------------------------------
;
; File : inequalities.lisp
; Author : Julien Schmaltz
; April 2003
; TIMA - VDS
; Grenoble, France
;------------------------------------------------------------------------

(in-package "ACL2")


(include-book "../../../../arithmetic/top")


;-----------------------------------------------------------------------
;
;
; Conclusion to reach: a*b + c < P*b
;
; Hypotheses : a, b, c, P are naturals
;              a <= P - 1
;              c <= b - 1
;
;
;
; Intermediate Theorem: a*b + c <= P*b - 1
;
;-------------------------------------------------------------------------

; the "majorant" of the sum is the sum of the majorants

(defthm maj_sum_=_sum_maj
  (implies (and (integerp a) (integerp b)
		(integerp alpha) (<= 0 a) (<= a alpha))
	   (<= (+ a b) (+ alpha b))))
; Prove 0.00

; for positives the majorant of the product is the product of the majorants

(defthm maj_prod_=_prod_maj
  (implies (and (integerp a) (integerp b) (< 0 b)
		(integerp alpha) (<= 0 a) (<= a alpha))
	   (<= (* a b) (* alpha b)))
  :hints (("GOAL" :in-theory (disable COMMUTATIVITY-OF-* DISTRIBUTIVITY))))
; Prove 0.01

; PROOF OF THE INTERMEDIATE THEOREM

(defthm lemma1
  (implies (and (integerp a) (integerp b) (integerp c)
		(<= 0 a) (< 0 b) (integerp alpha) (<= (* a b) (* alpha b)))
	   (<= (+ (* a b) c) (+ (* alpha b) c))))
; Prove 0.00

(defthm lemma2
  (implies (and (integerp a) (integerp b) (integerp c)
		(<= 0 a) (< 0 b) (integerp alpha) (<= a alpha))
	   (<= (+ (* a b) c) (+ (* alpha b) c)))
  :hints (("GOAL" :use (:instance maj_prod_=_prod_maj)
	   :in-theory (disable maj_prod_=_prod_maj COMMUTATIVITY-OF-+))))
; Prove 0.13

(defthm lemma3
  (implies (and (integerp a) (integerp b) (integerp c)
		(<= 0 a) (< 0 b) (integerp alpha) (<= a alpha)
		(<= c (1- b)))
	   (<= (+ (* a b) c) (+ (* alpha b) (1- b))))
  :hints (("GOAL" :use (:instance lemma2)
	   :in-theory (disable lemma2))))
; Prove 0.03

(defthm intermediate_theorem
  (implies (and (integerp a) (integerp b) (integerp c)
		(<= 0 a) (< 0 b) (<= 0 c) (<= c (1- b))
		(<= a (1- P)) (integerp P))
	   (<= (+ (* a b) c) (+ (* (1- P) b) (1- b))))
  :hints (("GOAL" :use (:instance lemma3 (alpha (1- P)) )
	   :in-theory (disable COMMUTATIVITY-OF-* DISTRIBUTIVITY
                               COMMUTATIVITY-OF-+ lemma3))))

; final theorem

(defthm final_theorem
  (implies (and (integerp a) (integerp b) (integerp c)
		(<= 0 a) (< 0 b) (<= 0 c) (<= c (1- b))
		(<= a (1- P)) (integerp P))
	   (< (+ (* a b) c) (* P b)))
  :hints (("GOAL" :use (:instance intermediate_theorem)
	   :in-theory (disable intermediate_theorem))))

; Prove 0.05

;Summary
;Form:  (CERTIFY-BOOK "inequalities" ...)
;Rules: NIL
;Warnings:  None
;Time:  3.71 seconds (prove: 0.26, print: 0.04, other: 3.41)
; "/h3/schmaltz/These/ACL2_Workshop/2003/Support/inequalities.lisp"

