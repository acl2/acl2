; A trivial clause-processor
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defevaluator empty-eval empty-eval-list nil)

;; Return a list of one clause (the same one we started with)
(defund do-nothing-clause-processor (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (progn$ (cw "Len of clause is ~x0.~%" (len clause))
          (cw "Literals are ~x0.~%" clause)
          (list clause)))

(defthm logic-term-list-listp-of-do-nothing-clause-processor
  (implies (logic-term-listp clause w)
           (logic-term-list-listp (do-nothing-clause-processor clause) w))
  :hints (("Goal" :in-theory (enable do-nothing-clause-processor))))

(defthm do-nothing-clause-processor-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (empty-eval (conjoin-clauses (do-nothing-clause-processor clause)) a)
                )
           (empty-eval (disjoin clause) a))
  :rule-classes ((:clause-processor
                  :well-formedness-guarantee logic-term-list-listp-of-do-nothing-clause-processor))
  :hints (("Goal" :in-theory (enable do-nothing-clause-processor))))
