; Copyright (C) 2007 by Shant Harutunian
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

;; Apply the given list of hints in sequence on every instance
;; of stable under simplification of the current clause
;; The hint sequence made available to the subgoals
;; depends on restart-on-new-id and counter.
;; Counter indicates the current position of the
;; hint to be used from the hint-lst.
;; If restart-on-new-id is t, then start from the
;; beginning of the hint-lst for a child goal.
;; If restart-on-new-id is nil, then start from the
;; counter position in the hint-lst for a child goal.

(defun staged-hints (stable-under-simplificationp
                     restart-on-new-id
                     hint-lst
                     id
                     last-id
                     counter)
  (let ((calc-last-id (if (equal id nil) 'id (list 'quote id))))
    (cond ((and stable-under-simplificationp (not (endp hint-lst)))
           (cond
            ((and restart-on-new-id
                  (not (equal id last-id)))
             (append `(:computed-hint-replacement
                       ((staged-hints stable-under-simplificationp
                                      ,restart-on-new-id
                                      ,(list 'quote hint-lst)
                                      id ,calc-last-id 1)))
                     (nth 0 hint-lst)))
            ((< counter (len hint-lst))
             (append `(:computed-hint-replacement
                       ((staged-hints stable-under-simplificationp
                                      ,restart-on-new-id
                                      ,(list 'quote hint-lst)
                                      id ,calc-last-id ,(1+ counter))))
                     (nth counter hint-lst)))
            (t nil)))
          (t nil))))
#|
;; Example use of staged-hints
(set-default-hints '((staged-hints
                      stable-under-simplificationp
                      nil ;;restart on new id
                      '((:in-theory (enable abs
                                            equal-cancel-divisors
                                            <-cancel-divisors)))
                      nil nil 0)))
|#

;; It is assumed that the symbol hyps represents
;; 1) a list of predicates that are conjoined in a hypothesis of
;; a goal, or 2) a list of only one predicate (not conjoined
;; with any predicate) which is the hypothesis of a goal.
;; The function scans through the list.
;; If the predicate is an inequality (< or <=), then an
;; :instance form to be used in a :use hint
;; is generated, where the :instance form is (:instance
;; standard-part-<= (x a) (y b)), where the symbols a and b
;; represent the first and second arguments, respectively,
;; of the inequality predicate.
;; If the predicate is not an inequality (< or <=), then it is ignored.
;; The function returns a list of :instance forms,
;; where each :instance form
;; corresponds to an inequality predicate in hyps. If no inequality
;; predicates (< or <=) are members of
;; hyps, then the function returns nil.
;;
;; The rewrite rule STANDARD-PART-<= should be disabled
;; so that the rewriter does not rewrite to true
;; the added hypothesis resulting from the :use hint.

(defun make-standard-part-<=-hint-from-hyps (hyps)
  (cond
   ((atom hyps) nil)
   ((or (equal (caar hyps) '<=)
        (equal (caar hyps) '<)) (append `((:instance standard-part-<=
                                                     (x ,(nth 1 (car hyps)))
                                                     (y ,(nth 2 (car hyps)))))
        (make-standard-part-<=-hint-from-hyps
         (cdr hyps))))
   (t (make-standard-part-<=-hint-from-hyps (cdr hyps)))))

;; Explore the given clause, and attempt to generate a hint from it.
;; If the clause is not an implication, no hint is generated
;; (nil is returned).
;; If the hypothesis is a conjunct of predicates,
;; then a list is generated whose elements
;; are the conjuncts. This list is passed to
;; make-standard-part-<=-hint-from-hyps.
;; If the hypothesis is not a conjunct, then a list is
;; generated consisting only of this hypothesis.
;; This list is then passed to
;; make-standard-part-<=-hint-from-hyps.
;; If the results of the call to
;; make-standard-part-<=-hint-from-hyps is nil, then
;; no hint is generated and nil is returned.
;; If the results of the call to make-standard-part-<=-hint-from-hyps
;; is non-nil, then this result is used to form and return a
;; use hint of the form (:use (t1 ... tn)), where each of
;; t1...tn are of the form
;; (:instance standard-part-<= (x a) (y b)),
;; where the symbols a and b represent the first and second
;; arguments, respectively, of an inequality predicate
;; (either < or <=) which appears in the list
;; passed to make-standard-part-<=-hint-from-hyps, and n
;; represents the number of inequality predicates (either < or <=)
;; which appear in this list. One such ti, 1<=i<=n, is generated for
;; each inequality predicate (either < or <=) which appears in this list.
;; It is assumed that this function is to be called from a
;; computed hint, and that the computed hint fires only when
;; stable-under-simplificationp is true.

(defun make-standard-part-<=-hint (clause)
  (cond
   ((and (equal (car clause) 'implies)
         (equal (caadr clause) 'and))
    (let ((hints (make-standard-part-<=-hint-from-hyps (cdadr clause))))
      (if (not (equal hints nil))
          `(:use ,hints)
        nil)))
   ((and (equal (car clause) 'implies))
    (let ((hints (make-standard-part-<=-hint-from-hyps
                  (list (cadr clause)))))
      (if (not (equal hints nil))
          `(:use ,hints)
        nil)))
   (t nil)))

(defun standard-part-hint (stable-under-simplificationp clause)
  (declare (xargs :mode :program))
  (cond (stable-under-simplificationp
         (make-standard-part-<=-hint (prettyify-clause clause nil nil)))
        (t nil)))
