; A very simple trivial clause-processor
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A slightly less trivial clause processor, compared to the one in
;; do-nothing.lisp.  We rebuild the clause by applying an identify function to
;; each literal.

(include-book "kestrel/evaluators/defevaluator-plus" :dir :system)

(local (in-theory (disable alistp disjoin disjoin2)))

(defevaluator+ if-eval if)

;; Returns the literal unchanged
(defund do-nothing-to-literal (lit)
  (declare (xargs :guard (pseudo-termp lit)))
  (progn$ (cw "Literal: ~x0~%" lit)
          lit))

;; in general, we can strengthen the literal because that just makes the new clause harder to prove
;; todo: consider using a constrained function with just this constraint
(defthm do-nothing-to-literal-correct
  (implies (and (if-eval (do-nothing-to-literal lit) a)
                (alistp a)
                (pseudo-termp lit))
           (if-eval lit a))
  :hints (("Goal" :in-theory (enable do-nothing-to-literal))))

(defund do-nothing-to-literals (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (if (endp clause)
      nil
    (cons (do-nothing-to-literal (first clause))
          (do-nothing-to-literals (rest clause)))))

;; Return a list of one clause (a copy of the one we started with)
(defund do-nothing-to-literals-clause-processor (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (progn$ (cw "Len of clause is ~x0.~%" (len clause))
          (cw "Literals are ~x0.~%" clause)
          (list (do-nothing-to-literals clause))))

(defthm do-nothing-to-literals-correct
  (implies (and (if-eval (disjoin (do-nothing-to-literals clause)) a)
                (alistp a)
                (pseudo-term-listp clause))
           (if-eval (disjoin clause) a))
  :hints (("Goal" :in-theory (enable do-nothing-to-literals))))

;todo: add :well-formedness proof
(defthm do-nothing-to-literals-clause-processor-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (if-eval (conjoin-clauses (do-nothing-to-literals-clause-processor clause)) a))
           (if-eval (disjoin clause) a))
  :rule-classes :clause-processor
  :hints (("Goal" :in-theory (enable do-nothing-to-literals-clause-processor))))
