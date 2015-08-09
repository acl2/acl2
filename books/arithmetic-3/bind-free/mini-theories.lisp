; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; mini-theories.lisp
;;;
;;;
;;; This book contains a couple of rules which don't seem to fit
;;; anywhere else.  They are sometimes useful, however, and
;;; their existence should be kept in mind.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local
 (include-book "mini-theories-helper"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Some people prefer to eliminate unary-- and unary-/.  The following
;;; two rules do exactly this.

;;; Be sure to disable |(* -1 x)|, if you enable this.

(defthm |(- x)|
  (equal (- x)
         (* -1 x)))

(in-theory (disable |(- x)|))

(theory-invariant (not (and (active-runep '(:rewrite |(* -1 x)|))
                            (active-runep '(:rewrite |(- x)|))))
                  :error t)

;;; Be sure to disable |(expt x -1)|, if you enable this.

(defthm |(/ x)|
    (equal (/ x)
           (expt x -1))
  :hints (("Goal" :expand (expt x -1))))

(in-theory (disable |(/ x)|))

(theory-invariant (not (and (active-runep '(:rewrite |(expt x -1)|))
                            (active-runep '(:rewrite |(/ x)|))))
                  :error t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Some proofs of linear inequalities don't work when presented as
;;; equalities.  This lemma allows you to state the equality as
;;; an equality rewrite rule, but breaks the equality apart for
;;; the proof.

;;; The same technique is sometimes needed for other boolean
;;; operators.

;;; Try the following lemma in a fresh ACL2 with and without
;;; rewrite-linear-equalities-to-iff to see what is meant by the
;;; above paragraphs:

#|(defthm <-*-0
  (implies (and (rationalp x)
                (rationalp y))
           (equal (< (* x y) 0)
                (and (not (equal x 0))
                     (not (equal y 0))
                     (iff (< x 0)
                          (< 0 y))))))|#


(defthm rewrite-linear-equalities-to-iff
   (equal (equal (< w x) (< y z))
          (iff (< w x) (< y z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; I put this lemma here because it makes me unhappy to have it
;;; anywhere else.  It serves as a reminder that type-set does
;;; not execute anything when relieving hypotheses.  This lack
;;; has irritated me at times.


; Matt K. change for v2-9: Now that terms are kept in quote-normal form, the
; following is illegal because the term translates to T.
#|
(defthm hack-minus-1
  (not (integerp (* 1/2 -1)))
  :rule-classes :type-prescription)
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The next six rules are gathered up into a single theory,
;;; strong-expt-type-prescription-rules and disabled in top.lisp.
;;; They are too expensive for daily wear, but are occasionally
;;; useful.

(defthm expt-type-prescription-negative-base-even-exponent
  (implies (and (< r 0)
		(rationalp r)
		(integerp i)
		(integerp (* 1/2 i)))
	   (< 0 (expt r i)))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-negative-base-odd-exponent
  (implies (and (< r 0)
		(rationalp r)
		(integerp i)
		(not (integerp (* 1/2 i))))
	   (< (expt r i) 0))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-nonpositive-base-even-exponent
  (implies (and (<= r 0)
                (rationalp r)
		(integerp i)
		(integerp (* 1/2 i)))
           (<= 0 (expt r i)))
  :rule-classes (:type-prescription :generalize)
  :hints (("Goal" :use ((:instance
			 expt-type-prescription-negative-base-even-exponent)))))

(defthm expt-type-prescription-nonpositive-base-odd-exponent
  (implies (and (<= r 0)
                (rationalp r)
		(integerp i)
		(not (integerp (* 1/2 i))))
           (<= (expt r i) 0))
  :rule-classes (:type-prescription :generalize)
  :hints (("Goal" :use ((:instance
			 expt-type-prescription-negative-base-odd-exponent)))))

(defthm expt-negative-base-even-exponent
  (implies (and (rationalp r)
		(integerp i)
		(integerp (* 1/2 i)))
	   (equal (expt (* -1 r) i)
		  (expt r i))))

(defthm expt-negative-base-odd-exponent
  (implies (and (rationalp r)
		(integerp i)
		(not (integerp (* 1/2 i))))
	   (equal (expt (* -1 r) i)
		  (* -1 (expt  r i)))))
