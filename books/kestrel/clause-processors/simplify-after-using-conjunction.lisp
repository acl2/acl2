; A clause-processor that helps after :use-ing a conjunction
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/clause-processors/subst-flag" :dir :system)
(include-book "kestrel/clause-processors/flatten-literals" :dir :system)
(include-book "kestrel/clause-processors/simple-subsumption" :dir :system)
(include-book "kestrel/clause-processors/push-unary-functions" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-list-listp" :dir :system))

(local (in-theory (disable disjoin)))

;; TODO: Have my-make-flag (or make-flag) put in the :ruler-extenders of the old function by default.

(defevaluator+ my-make-flag-eval if equal eql eq not
  booland boolor boolif myif ;todo
  )

;changes the evaluator
(defthm resolve-ifs-in-clause-correct-new
  (iff (my-make-flag-eval (disjoin (resolve-ifs-in-clause clause nil nil)) a)
       (my-make-flag-eval (disjoin clause) a))
  :hints (("Goal" :use (:functional-instance
                        resolve-ifs-in-clause-correct-special
                        (equality-eval my-make-flag-eval)
                        (equality-eval-list my-make-flag-eval-list)))))

;changes the evaluator
(defthm my-make-flag-eval-of-disjoin-of-flatten-disjuncts
  (iff (my-make-flag-eval (disjoin (flatten-disjuncts clause)) a)
       (my-make-flag-eval (disjoin clause) a))
  :hints (("Goal" :use (:functional-instance
                        con-and-dis-eval-of-disjoin-of-flatten-disjuncts
                        (con-and-dis-eval my-make-flag-eval)
                        (con-and-dis-eval-list my-make-flag-eval-list)))))

;changes the evaluator
(defthm my-make-flag-eval-of-disjoin-of-sublis-var-and-simplify-lst
  (implies (and (alistp a)
                (pseudo-term-listp clause))
           (iff (my-make-flag-eval (disjoin (sublis-var-and-simplify-lst nil clause nil nil)) a)
                (my-make-flag-eval (disjoin clause) a)))
  :hints (("Goal" :use (:functional-instance
                        equality-eval-of-disjoin-of-sublis-var-and-simplify-lst-special
                        (equality-eval my-make-flag-eval)
                        (equality-eval-list my-make-flag-eval-list)))))

;changes the evaluator
(defthm my-make-flag-eval-of-disjoin-of-push-unary-functions-in-literals
  (implies (and (symbol-listp unary-fns)
                (alistp a)
                (pseudo-term-listp clause))
           (iff (my-make-flag-eval (disjoin (push-unary-functions-in-literals clause unary-fns)) a)
                (my-make-flag-eval (disjoin clause) a)))
  :hints (("Goal" :use (:functional-instance
                        if-eval-of-disjoin-of-push-unary-functions-in-literals
                        (if-eval my-make-flag-eval)
                        (if-eval-list my-make-flag-eval-list)))))

;changes the evaluator
(defthm my-make-flag-eval-of-conjoin-of-disjoin-lst-of-clause-to-clause-list
  (iff (my-make-flag-eval (conjoin (disjoin-lst (clause-to-clause-list clause))) a)
       (my-make-flag-eval (disjoin clause) a))
  :hints (("Goal" :use (:functional-instance
                        equality-eval-of-conjoin-of-disjoin-lst-of-clause-to-clause-list
                        (equality-eval my-make-flag-eval)
                        (equality-eval-list my-make-flag-eval-list)))))

;changes the evaluator
(defthm my-make-flag-eval-of-disjoin-of-handle-constant-literals
  (iff (my-make-flag-eval (disjoin (handle-constant-literals clause)) a)
       (my-make-flag-eval (disjoin clause) a))
  :hints (("Goal" :use (:functional-instance
                        equality-eval-of-disjoin-of-handle-constant-literals
                        (equality-eval my-make-flag-eval)
                        (equality-eval-list my-make-flag-eval-list)))))

(defun simplify-after-using-conjunction-clause-processor (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (let* ( ;(clause (first (sublis-var-and-simplify-clause-processor clause)))
         (new-clause (first (flatten-literals-clause-processor clause)))
         ;;(clause (first (push-o-p-clause-processor clause))) ;this is a bit out of place here
         (clauses (simple-subsumption-clause-processor new-clause)) ;todo: doesn't yet deal with the o-p claims because they appear not as conjuncts
         ;; (changep (not (equal clauses (list clause)))) ;todo: optimize
         )
    (progn$ ;; (if changep
            ;;     (cw "(Before: ~X01)%(After: ~X23)~%" clause nil new-clause nil)
            ;;   (cw "No change made by simplify-after-using-conjunction-clause-processor.~%"))
            clauses)))

;todo: add :well-formedness proof
(defthm simplify-after-using-conjunction-clause-processor-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (my-make-flag-eval (conjoin-clauses (simplify-after-using-conjunction-clause-processor clause)) a))
           (my-make-flag-eval (disjoin clause) a))
  :rule-classes :clause-processor
  :hints (("Goal" :in-theory (e/d ( ;sublis-var-and-simplify-clause-processor
                                   simple-subsumption-clause-processor
                                   FLATTEN-LITERALS-CLAUSE-PROCESSOR
                                   SUBLIS-VAR-AND-SIMPLIFY-CLAUSE-PROCESSOR
                                   PUSH-O-P-CLAUSE-PROCESSOR
                                   )
                                  (DISJOIN-LST)))))
