

;; This is a computed hint that causes a :by hint to be applied to a subgoal
;; when the first hyp in the clause is (use-by-hint thmname).

;; This can enable clause processors to make use of user-provided,
;; pre-proven ACL2 theorems.  For example, assume a clause processor does
;; something with user-provided theorems and the following theorem is provided
;; to it by the user:
;; (defthm foo-thm (implies (bar x) (equal (foo x) 'baz)))
;; In general, to use the fact provided by this theorem, the clause processor
;; must prove this theorem again.  A quick/easy way to do this is to produce
;; the clause
;; `((not (use-by-hint 'foo-thm))
;;   (implies (bar x) (equal (foo x) 'baz)))
;; If the user (or, say, a computed hint that calls the clause processor)
;; ensures that a (use-by-computed-hint clause) fires when ACL2 attempts to
;; prove this clause, it should then be discharged immediately.

;; See also clause-processors/multi-env-trick for additional help with making
;; clause processors that use user-provided lemmas.

(in-package "ACL2")

(include-book "join-thms")

;; USE-BY-HINT is t.  Therefore it can be added as a hyp to any subgoal without
;; affecting its truth value.  It serves to signal use-by-computed-hint to give
;; a particular :by hint.
(defun use-by-hint (x)
  (declare (ignore x))
  t)

(in-theory (disable use-by-hint
                    (use-by-hint)
                    (:type-prescription use-by-hint)))


;; This is a very simple clause processor which simply removes the first
;; literal from the clause.
(defun remove-first-hyp-cp (clause)
  (if (consp clause)
      (list (cdr clause))
    (list clause)))

(defevaluator use-by-hint-ev use-by-hint-ev-lst
  ((if a b c)))

(def-join-thms use-by-hint-ev)

(defthm remove-first-hyp-cp-correct
  (implies (and (pseudo-term-listp x)
                (alistp a)
                (use-by-hint-ev (conjoin-clauses (remove-first-hyp-cp x))
                         a))
           (use-by-hint-ev (disjoin x) a))
  :rule-classes :clause-processor)

;; The computed hint.  Checks to see if the first literal in the clause is a
;; hyp of the form (use-by-hint 'rulename).  If so, first remove that literal
;; using remove-first-hyp-cp, then give a :by hint with that rule.
(defun use-by-computed-hint (clause)
  (and (consp clause)
       (let ((car (car clause)))
         (case-match car
           (('not ('use-by-hint ('quote rule)))
            `(:computed-hint-replacement
              ('(:by ,rule :do-not '(preprocess simplify)))
              :clause-processor remove-first-hyp-cp))
           (& nil)))))


