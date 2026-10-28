; A verified clause processor that generalizes terms
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; As a sanity check on the form of the main theorem, we use it to verify a
;; clause processor that builds a generalized clause the way generalize1
;; does.  The hint gives the terms to generalize and the new variables.  We
;; use no type restrictions and a world with no :generalize rules.

(include-book "generalize-proofs")
(local (include-book "kestrel/lists-light/intersectp-equal" :dir :system))

;; A world with no :generalize rules.
(defconst *generalize-clause-processor-world*
  '((generalize-rules global-value)))

(defund generalize-clause-processor-hint-okp (cl hint)
  (let ((terms (car hint))
        (vars (cadr hint)))
    (and (pseudo-term-listp terms)
         (generalization-vars-okp vars terms)
         (not (intersectp-equal vars (free-vars-in-terms cl)))
         (not (intersectp-equal vars (free-vars-in-terms terms))))))

(defund generalize-clause-processor (cl hint)
  (declare (xargs :guard t :verify-guards nil))
  (let ((terms (car hint))
        (vars (cadr hint)))
    (if (generalize-clause-processor-hint-okp cl hint)
        (mv-let (gr-seg alist)
          (generalize-rule-segment terms vars nil *generalize-clause-processor-world*)
          (declare (ignore alist))
          (list (sublis-expr-lst (pairlis$ terms vars)
                                 (disjoin-clauses nil
                                                  (disjoin-clauses gr-seg cl)))))
      (list cl))))

;; The alist under which the clause returned is evaluated: The new variables
;; are bound to the values of the terms.  This is a clause processor in the
;; general form described in :doc clause-processor, where the result clauses
;; are evaluated under a different alist.
(defund generalize-clause-processor-alist (cl hint a)
  (if (generalize-clause-processor-hint-okp cl hint)
      (generalization-alist (car hint) (cadr hint) a)
    a))

(defthm generalize-ev-of-conjoin-clauses-of-cons-and-nil
  (iff (generalize-ev (conjoin-clauses (list clause)) a)
       (generalize-ev (disjoin clause) a))
  :hints (("Goal" :in-theory (enable conjoin-clauses))))

(defthm generalize-clause-processor-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (generalize-ev (conjoin-clauses (generalize-clause-processor cl hint))
                               (generalize-clause-processor-alist cl hint a)))
           (generalize-ev (disjoin cl) a))
  :rule-classes :clause-processor
  :hints (("Goal" :use (:instance generalize-ev-when-generalize1-clause
                                  (terms (car hint))
                                  (vars (cadr hint))
                                  (tr-seg nil)
                                  (ens nil)
                                  (wrld *generalize-clause-processor-world*))
           :in-theory (e/d (generalize-clause-processor
                            generalize-clause-processor-alist
                            generalize-clause-processor-hint-okp)
                           (generalize-ev-of-disjoin
                            conjoin-clauses
                            sublis-expr-lst
                            disjoin-clauses
                            generalize-rule-segment
                            generalization-alist
                            generalization-vars-okp)))))

;; Example: Generalizing (append x y) to z leaves a goal that is true.
(defthm generalize-clause-processor-test
  (implies (true-listp (append x y))
           (equal (append (append x y) nil)
                  (append x y)))
  :hints (("Goal" :clause-processor (generalize-clause-processor clause '(((binary-append x y)) (z)))))
  :rule-classes nil)
