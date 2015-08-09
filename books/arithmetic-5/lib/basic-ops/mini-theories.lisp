; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; mini-theories.lisp
;;;
;;; This book contains a couple of rules which don't seem to fit
;;; anywhere else.  They are sometimes useful, however, and
;;; their existence should be kept in mind.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

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


;;; After J gets the ``or hint'' into ACL2, consider using it with the
;;; following rule when things are stable-under-simplificationp to
;;; conditionally try rewriting equal to iff.

;;; Taken from rtl/rel5/arithmetic/predicate.lisp

;;; Rewrites an equality of two "predicates" to, essentially, an iff.
;;; This can save you from having to do two proofs, one for each of
;;; the forward and back directions.

;;; Feel free to add more predicates to this list as time goes on.

(defun predicate-p (term)
  (and (consp term) ;drop this test?
       (member (car term) '(equal <
			    integerp rationalp
			    #+non-standard-analysis realp
			    complex-rationalp
			    #+non-standard-analysis complexp
			    ))))

;;; This can cause case-splits, but that's sort of the point.

(defthm equal-of-predicates-rewrite
  (implies (and (syntaxp (and (predicate-p a)
                              (predicate-p b)))
                (booleanp a)
                (booleanp b))
           (equal (equal a b)
		  (iff a b))))