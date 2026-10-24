; Correctness of the ACL2 system function termify-clause-set
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TERMIFY-CLAUSE-SET (in induct.lisp) turns a set of clauses into a single
;; term that is true when all the clauses are true.  It is soundness-critical:
;; the termination and guard conjectures of definitions are proved in the form
;; it produces (see prove-termination and prove-guard-clauses in defuns.lisp),
;; and it builds the formulas of :termination-theorem and :guard-theorem lemma
;; instances (see termination-theorem and guard-theorem in
;; history-management.lisp).

;; We state its correctness using IF-EVAL, which knows only IF, and the
;; standard meaning of a clause set, CONJOIN-CLAUSES (see :DOC
;; clause-processor).

(include-book "kestrel/evaluators/if-eval" :dir :system)
(local (include-book "cons-term-helpers"))
(local (include-book "kestrel/terms-light/termp" :dir :system))

;; Cons-term evaluates calls of IF on constants, as IF-EVAL would.

(local
 (defthm quote-listp-of-cdr
   (implies (quote-listp args)
            (quote-listp (cdr args)))))

(local
 (defthm if-eval-of-car-when-quote-listp
   (implies (quote-listp args)
            (equal (if-eval (car args) a)
                   (unquote (car args))))))

(local
 (defthm if-eval-of-cons-term-of-if
   (equal (if-eval (cons-term 'if args) a)
          (if-eval (cons 'if args) a))
   :hints (("Goal" :in-theory (enable cons-term cons-term1)))))

;; The result is true exactly when all the clauses are true.  The
;; true-listp hypothesis is implied by the guard (see the counterexample in
;; termify-clause-set-tests.lisp).
(defthm termify-clause-set-correct
  (implies (true-listp clauses)
           (iff (if-eval (termify-clause-set clauses) a)
                (if-eval (conjoin-clauses clauses) a)))
  :hints (("Goal" :in-theory (e/d (termify-clause-set conjoin-clauses)
                                  (cons-term)))))

;; Without the true-listp hypothesis, the result can be false when
;; CONJOIN-CLAUSES is true, since termify-clause-set tests for the end of the
;; list with NULL but disjoin-lst uses ENDP: see
;; termify-clause-set-incorrect-without-true-listp in
;; termify-clause-set-tests.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TERMIFY-CLAUSE-SET makes a term from clauses of terms.  (For termp, IF
;; must have its usual arity.  Termp implies no-nils-in-termp,
;; lambdas-closed-in-termp, and no-duplicate-lambda-formals-in-termp.)

(local
 (defthm pseudo-termp-of-disjoin
   (implies (pseudo-term-listp clause)
            (pseudo-termp (disjoin clause)))
   :hints (("Goal" :in-theory (enable disjoin disjoin2)))))

(local
 (defthm termp-of-disjoin
   (implies (and (term-listp clause w)
                 (equal (arity 'if w) 3))
            (termp (disjoin clause) w))
   :hints (("Goal" :in-theory (enable disjoin disjoin2 termp)))))

(defthm pseudo-termp-of-termify-clause-set
  (implies (pseudo-term-list-listp clauses)
           (pseudo-termp (termify-clause-set clauses)))
  :hints (("Goal" :in-theory (e/d (termify-clause-set) (cons-term)))))

(defthm termp-of-termify-clause-set
  (implies (and (term-list-listp clauses w)
                (equal (arity 'if w) 3))
           (termp (termify-clause-set clauses) w))
  :hints (("Goal" :in-theory (e/d (termify-clause-set termp) (cons-term)))))
