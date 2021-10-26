; Turning a clause into a clause list

; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/evaluators/if-eval" :dir :system)

(defund clause-to-clause-list (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (if (equal clause '('t))
      nil ; no more clauses to prove
    (list clause)))

(defthm if-eval-of-conjoin-of-disjoin-lst-of-clause-to-clause-list
  (iff (if-eval (conjoin (disjoin-lst (clause-to-clause-list clause))) a)
       (if-eval (disjoin clause) a))
  :hints (("Goal" :in-theory (enable clause-to-clause-list))))
