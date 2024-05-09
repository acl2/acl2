; Helper functions for manipulating calls of case
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Justifies calling strip-cadrs on the clauses
(defthm legal-case-clausesp-forward-to-all->=-len
  (implies (legal-case-clausesp clauses)
           (all->=-len clauses 2))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable all->=-len legal-case-clausesp))))

(defthm legal-case-clausesp-forward-to-alistp
  (implies (legal-case-clausesp clauses)
           (alistp clauses))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable alistp legal-case-clausesp))))
