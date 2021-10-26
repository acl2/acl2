; A clause processor to simplify assumptions by dropping weaker conjuncts
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "clause-to-clause-list")
(include-book "kestrel/terms-light/simplify-conjunction" :dir :system)
(include-book "kestrel/evaluators/if-and-not-eval" :dir :system)

;dup
;; just changes the evaluator
(defthm if-and-not-eval-of-conjoin-of-disjoin-lst-of-clause-to-clause-list
  (iff (if-and-not-eval (conjoin (disjoin-lst (clause-to-clause-list clause))) a)
       (if-and-not-eval (disjoin clause) a))
  :hints (("Goal" :use (:functional-instance if-eval-of-conjoin-of-disjoin-lst-of-clause-to-clause-list
                                             (if-eval if-and-not-eval)
                                             (if-eval-list if-and-not-eval-list)))))

;; Correctness of drop-clearly-implied-conjuncts.
(defthm if-and-not-eval-of-drop-clearly-implied-conjuncts
  (implies (all-eval-to-true-with-if-and-not-eval true-terms a)
           (iff (if-and-not-eval (drop-clearly-implied-conjuncts term true-terms) a)
                (if-and-not-eval term a)))
  :hints (("Goal" :use (:functional-instance if-eval-of-drop-clearly-implied-conjuncts
                                             (all-eval-to-true-with-if-eval all-eval-to-true-with-if-and-not-eval)
                                             (if-eval if-and-not-eval)
                                             (if-eval-list if-and-not-eval-list)))))

;; Returns a new clause.
;; TODO: Use assumption info from previous literals?
(defund simplify-assumptions-in-clause (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (if (endp clause)
      nil
    (let ((new-lit (let ((lit (first clause)))
                     (if (and (call-of 'not lit)
                              (= 1 (len (fargs lit))))
                         `(not ,(drop-clearly-implied-conjuncts (farg1 lit) nil))
                       lit))))
      (cons new-lit
            (simplify-assumptions-in-clause (rest clause))))))

(defthm pseudo-term-listp-of-simplify-assumptions-in-clause
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp (simplify-assumptions-in-clause clause)))
  :hints (("Goal" :in-theory (enable simplify-assumptions-in-clause))))

(defthm all-eval-to-false-with-if-and-not-eval-of-simplify-assumptions-in-clause
  (iff (all-eval-to-false-with-if-and-not-eval (simplify-assumptions-in-clause clause) a)
       (all-eval-to-false-with-if-and-not-eval clause a))
  :hints (("Goal" :in-theory (e/d (simplify-assumptions-in-clause) ()))))

;; ;;move
;; ;; Correctness of simplify-assumptions.
;; (defthm if-and-not-eval-of-simplify-assumptions-in-clause
;;   (iff (if-and-not-eval (disjoin (simplify-assumptions-in-clause clause)) a)
;;        (if-and-not-eval (disjoin clause) a)))

(defund simplify-assumptions-clause-processor (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (let* ((clause (simplify-assumptions-in-clause clause))
         ;; (clause (handle-constant-literals clause))
         )
    (clause-to-clause-list clause)))

;todo: add :well-formedness proof
(defthm simplify-assumptions-clause-processor-correct
  (implies (if-and-not-eval (conjoin-clauses (simplify-assumptions-clause-processor clause)) a)
           (if-and-not-eval (disjoin clause) a))
  :rule-classes :clause-processor
  :hints (("Goal" :in-theory (enable simplify-assumptions-clause-processor))))
