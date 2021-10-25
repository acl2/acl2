; A clause processor that handles constant literals in a clause

; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "clause-to-clause-list")
(include-book "kestrel/evaluators/equality-eval" :dir :system)
(include-book "kestrel/evaluators/if-eval" :dir :system)

;; Returns a new, equivalent clause.
(defun handle-constant-literals (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (if (endp clause)
      nil
    (let ((lit (first clause)))
      (if (quotep lit)
          (if (unquote lit)
              (list *t*) ; a non-nil constant literal proves the clause
            ;; drop this, lit, which must be *nil*:
            (handle-constant-literals (rest clause)))
        (let ((rest-res (handle-constant-literals (rest clause))))
          (if (equal '('t) rest-res)
              rest-res
            (cons lit rest-res)))))))

(defthm if-eval-of-disjoin-of-handle-constant-literals
  (iff (if-eval (disjoin (handle-constant-literals clause)) a)
       (if-eval (disjoin clause) a))
  :hints (("Goal" :in-theory (enable disjoin))))

(defthm pseudo-term-listp-of-handle-constant-literals
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp (handle-constant-literals clause)))
  :hints (("Goal" :in-theory (enable handle-constant-literals))))

(defund handle-constant-literals-clause-processor (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (let* ((clause (handle-constant-literals clause)))
    (clause-to-clause-list clause)))

;todo: add :well-formedness proof
(defthm handle-constant-literals-clause-processor-correct
  (implies (if-eval (conjoin-clauses (handle-constant-literals-clause-processor clause)) a)
           (if-eval (disjoin clause) a))
  :rule-classes :clause-processor
  :hints (("Goal" :in-theory (enable handle-constant-literals-clause-processor))))
