; Soundness of the clause built by generalization
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Generalize-clause, the waterfall's generalization process, calls
;; generalize1 to build its result clause:
;;
;;   (sublis-expr-lst (pairlis$ terms vars)
;;                    (disjoin-clauses tr-seg
;;                                     (disjoin-clauses gr-seg cl)))
;;
;; Here TERMS are the terms being generalized, VARS are the new variables,
;; TR-SEG (computed by type-restriction-segment using type-set) contains the
;; negations of facts about the types of the terms, and GR-SEG (computed by
;; generalize-rule-segment) contains the negations of instances of
;; :generalize rules.
;;
;; We prove that this clause is sound: If it is true when the new variables
;; are bound to the values of the terms, then the original clause is true.
;; This requires that the type restrictions in TR-SEG are true (we cannot
;; prove this here, because type-set cannot be put into :logic mode this way)
;; and that the :generalize rules are theorems.  It also requires that the new
;; variables be fresh: generalize-clause chooses them (using
;; generate-variable-lst, which also calls type-set) to avoid the variables of
;; the clause.  We show that the variables of GR-SEG are among those of the
;; terms, so they need not be avoided separately.

(include-book "sublis-expr-proofs")
(include-book "generalize-rule-proofs")
(local (include-book "helpers"))

(local (in-theory (disable generalize-ev-of-fncall-args)))

;; Replacing the terms by the variables preserves the meaning of a clause.
(defthm all-eval-to-false-with-generalize-ev-of-sublis-expr-lst
  (implies (and (generalization-vars-okp vars terms)
                (not (intersectp-equal vars (free-vars-in-terms cl)))
                (pseudo-term-listp cl))
           (equal (all-eval-to-false-with-generalize-ev (sublis-expr-lst (pairlis$ terms vars) cl)
                                                        (generalization-alist terms vars a))
                  (all-eval-to-false-with-generalize-ev cl a)))
  :hints (("Goal" :induct (len cl)
           :in-theory (e/d (sublis-expr-lst) (sublis-expr))
           :expand ((free-vars-in-terms cl)))))

;; The main theorem: The clause built by generalize1 is sound.
(defthm generalize-ev-when-generalize1-clause
  (implies (and (generalize-ev (disjoin (sublis-expr-lst
                                         (pairlis$ terms vars)
                                         (disjoin-clauses
                                          tr-seg
                                          (disjoin-clauses
                                           (mv-nth 0 (generalize-rule-segment terms vars ens wrld))
                                           cl))))
                               (generalization-alist terms vars a))
                ;; The type restrictions are true.  TR-SEG holds their
                ;; negations, as clause literals (hypotheses of the
                ;; generalized clause), so they are true when all of these
                ;; literals are false:
                (all-eval-to-false-with-generalize-ev tr-seg a)
                ;; The :generalize rules are theorems:
                (generalize-rules-okp (global-val 'generalize-rules wrld))
                ;; The new variables are fresh:
                (generalization-vars-okp vars terms)
                (not (intersectp-equal vars (free-vars-in-terms cl)))
                (not (intersectp-equal vars (free-vars-in-terms terms)))
                (not (intersectp-equal vars (free-vars-in-terms tr-seg)))
                (pseudo-term-listp cl)
                (pseudo-term-listp terms)
                (pseudo-term-listp tr-seg))
           (generalize-ev (disjoin cl) a))
  :rule-classes nil
  :hints (("Goal" :use (:instance generalize-rule-segment-properties
                                  (vars2 vars))
           :in-theory (e/d (generalization-vars-okp)
                           (generalize-rule-segment-properties
                            generalize-rule-segment
                            disjoin-clauses
                            sublis-expr-lst)))))
