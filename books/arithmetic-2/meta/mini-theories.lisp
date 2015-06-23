; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; mini-theories.lisp
;;
;;
;; This book contains a couple of rules which don't seem to fit
;; anywhere else.  They are sometimes useful, however, and
;; their existence should be kept im mind.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local
 (include-book "../pass1/top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Some proofs of linear equalities don't work when presented as
;; equalities.  This lemma allows you to state the equality as
;; an equality rewrite rule, but breaks the equality apart for
;; the proof.
;;
;; Try the following lemma with and without
;; rewrite-linear-equalities-to-iff to see what is meant by the
;; above paragraph:

#|(defthm <-*-0
  (implies (and (real/rationalp x)
                (real/rationalp y))
           (equal (< (* x y) 0)
                (and (not (equal x 0))
                     (not (equal y 0))
                     (iff (< x 0)
                          (< 0 y))))))|#

;; The same technique is sometimes needed for other boolean
;; operators.


(defthm rewrite-linear-inequalities-to-iff
   (equal (equal (< w x) (< y z))
          (iff (< w x) (< y z))))

(in-theory (disable rewrite-linear-inequalities-to-iff))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I put this lemma here because it makes me unhappy to have it
;; anywhere else.  It serves as a reminder that type-set does
;; not execute anything when relieving hypotheses.  This lack
;; has irritated me at times.

; Matt K. change for v2-9: Now that terms are kept in quote-normal form, the
; following is illegal because the term translates to T.
#|
(defthm hack-minus-1
  (not (integerp (* 1/2 -1)))
  :rule-classes :type-prescription)
|#
