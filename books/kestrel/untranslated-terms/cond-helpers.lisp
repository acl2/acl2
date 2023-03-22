; Helper functions for manipulating calls of COND
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

(defund legal-cond-clausesp (clauses)
  (declare (xargs :guard t))
  (if (atom clauses)
      (null clauses)
    (let ((clause (first clauses)))
      (and (true-listp clause)
           (or (= 1 (len clause))
               (= 2 (len clause)))
           (legal-cond-clausesp (rest clauses))))))

(defthm legal-cond-clausesp-forward-to-true-listp
  (implies (legal-cond-clausesp clauses)
           (true-listp clauses))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable legal-cond-clausesp))))

;; The CLAUSES can have length 1 or 2.  All we have to do is flatten.
(defund extract-terms-from-cond-clauses (clauses)
  (declare (xargs :guard (legal-cond-clausesp clauses)
                  :guard-hints (("Goal" :in-theory (enable legal-cond-clausesp)))))
  (if (endp clauses)
      nil
    (append (true-list-fix (first clauses))
            (extract-terms-from-cond-clauses (rest clauses)))))

(defthm <=-of-acl2-count-of-extract-terms-from-cond-clauses-linear
  (<= (acl2-count (extract-terms-from-cond-clauses clauses))
      (acl2-count clauses))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable extract-terms-from-cond-clauses))))

;; Replace the terms in the CLAUSES with the corresponding NEW-TERMS, which
;; come in order and correspond to the terms in the existing CLAUSES.  Note
;; that each element of CLAUSES may have length 1 or 2.
(defund recreate-cond-clauses (clauses new-terms)
  (declare (xargs :guard (and (legal-cond-clausesp clauses)
                              (true-listp new-terms))
                  :guard-hints (("Goal" :in-theory (enable legal-cond-clausesp)))))
  (if (endp clauses)
      nil
    (let* ((clause (first clauses))
           (clause-len (len clause)) ;can be 1 or 2
           )
      (cons (take clause-len new-terms) ; the new clause
            (recreate-cond-clauses (rest clauses)
                                   (nthcdr clause-len new-terms))))))

(defthm legal-cond-clausesp-of-recreate-cond-clauses
  (implies (legal-cond-clausesp clauses)
           (legal-cond-clausesp (recreate-cond-clauses clauses new-terms)))
  :hints (("Goal" :in-theory (enable legal-cond-clausesp recreate-cond-clauses))))
