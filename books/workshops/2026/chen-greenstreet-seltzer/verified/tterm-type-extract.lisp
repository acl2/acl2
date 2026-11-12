;; Copyright (C) 2026, University of British Columbia
;; Written by Chris Chen
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

;;
;; This book defines a clause processor that extracts typing
;; information from unconditional, monomorphically-typed typed terms.

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "std/alists/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "xdoc/top" :dir :system)

(include-book "basics")
(include-book "hint-interface")
(include-book "smt-judgement")
(include-book "tterm")
(include-book "tterm-clause")

(set-state-ok t)
(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))

;; Extracts :var guts from a typed term, returning an alist of (sym
;; . judgement) pairs
(defsection SMT-tterm-type-extract
  :parents (verified)

  (define tterm->smt-judgement-symbol ((tterm tterm-p))
    :returns (rv symbolp)
    (b* ((tterm (tterm-fix tterm))
         (smt-j (tterm->smt-judgements tterm))
         ((unless (and (equal (len smt-j) 1)
                       (equal (len (car smt-j)) 2)))
          'acl2::any-p$inline))
      (symbol-fix (caar smt-j)))
    ///
    (fty::deffixequiv tterm->smt-judgement-symbol))

  (std::defprojection tterms->smt-judgement-symbols ((x tterm-list-p))
    :returns (rv symbol-listp)
    (tterm->smt-judgement-symbol x)
    ///
    (fty::deffixequiv tterms->smt-judgement-symbols))

  (defines tterm->fn-judgements
    :verify-guards nil
    :well-founded-relation l<

    (define tterm-if->fn-judgements ((tterm tterm-p))
      :measure (list (tterm->expr-count tterm) 2 0)
      :guard (equal (tterm->kind tterm) :if)
      :returns (rv fn-judgement-list-p)
      :flag if
      (b* ((tterm (tterm-fix tterm))
           ((unless (mbt (equal (tterm->kind tterm) :if))) nil)
           (condx-judgements (tterm->fn-judgements (tterm->condx tterm)))
           (thenx-judgements (tterm->fn-judgements (tterm->thenx tterm)))
           (elsex-judgements (tterm->fn-judgements (tterm->elsex tterm))))
        (append condx-judgements
                thenx-judgements
                elsex-judgements)))

    (define tterm-list->fn-judgements ((tterms tterm-list-p))
      :measure (list (tterm-list->expr-list-count tterms) 1 0)
      :returns (rv fn-judgement-list-p)
      :flag list
      (b* ((tterms (tterm-list-fix tterms)))
        (if (consp tterms)
            (append (tterm->fn-judgements (car tterms))
                    (tterm-list->fn-judgements (cdr tterms)))
          nil)))

    (define tterm-fncall->fn-judgements ((tterm tterm-p))
      :measure (list (tterm->expr-count tterm) 2 0)
      :guard (equal (tterm->kind tterm) :fncall)
      :returns (rv fn-judgement-list-p)
      :flag fncall
      (b* ((tterm (tterm-fix tterm))
           ((unless (mbt (equal (tterm->kind tterm) :fncall))) nil)
           (name (tterm->f tterm))
           (smt-j (tterm->smt-judgements tterm))
           ((unless (and (equal (len smt-j) 1)
                         (equal (len (car smt-j)) 2)))
            nil)
           (range (symbol-fix (caar smt-j)))
           (args (tterm->args tterm))
           (domain (tterms->smt-judgement-symbols args)))
        (cons (fn-judgement name domain range)
              (tterm-list->fn-judgements args))))

    (define tterm->fn-judgements ((tterm tterm-p))
      :measure (list (tterm->expr-count tterm) 3 0)
      :returns (rv fn-judgement-list-p)
      :flag term
      (b* ((tterm (tterm-fix tterm)))
        (case (tterm->kind tterm)
          (:quote nil)
          (:var nil)
          (:if (tterm-if->fn-judgements tterm))
          (:fncall (tterm-fncall->fn-judgements tterm))))
      ///
      (verify-guards tterm->fn-judgements)
      (fty::deffixequiv-mutual tterm->fn-judgements)))

  (define tterm-var->var-judgements ((tterm tterm-p))
    :guard (equal (tterm->kind tterm) :var)
    :returns (rv var-judgement-list-p)
    (b* ((tterm (tterm-fix tterm))
         ((unless (mbt (equal (tterm->kind tterm) :var))) nil)
         (smt-j (tterm->smt-judgements tterm))
         ((unless (and (equal (len smt-j) 1)
                       (equal (len (car smt-j)) 2)))
          nil)
         (name (tterm->name tterm))
         (recognizer (caar smt-j)))
      (list (var-judgement (symbol-fix name)
                           (symbol-fix recognizer))))
    ///
    (fty::deffixequiv tterm-var->var-judgements))

  (defines tterm->var-judgements
    :verify-guards nil
    :well-founded-relation l<

    (define tterm-if->var-judgements ((tterm tterm-p))
      :measure (list (tterm->expr-count tterm) 2 0)
      :guard (equal (tterm->kind tterm) :if)
      :returns (rv var-judgement-list-p)
      :flag if
      (b* ((tterm (tterm-fix tterm))
           ((unless (mbt (equal (tterm->kind tterm) :if))) nil)
           (condx-judgements (tterm->var-judgements (tterm->condx tterm)))
           (thenx-judgements (tterm->var-judgements (tterm->thenx tterm)))
           (elsex-judgements (tterm->var-judgements (tterm->elsex tterm))))
        (append condx-judgements
                thenx-judgements
                elsex-judgements)))

    (define tterm-list->var-judgements ((tterms tterm-list-p))
      :measure (list (tterm-list->expr-list-count tterms) 1 0)
      :returns (rv var-judgement-list-p)
      :flag list
      (b* ((tterms (tterm-list-fix tterms)))
        (if (consp tterms)
            (append (tterm->var-judgements (car tterms))
                    (tterm-list->var-judgements (cdr tterms)))
          nil)))

    (define tterm-fncall->var-judgements ((tterm tterm-p))
      :measure (list (tterm->expr-count tterm) 2 0)
      :guard (equal (tterm->kind tterm) :fncall)
      :returns (rv var-judgement-list-p)
      :flag fncall
      (b* ((tterm (tterm-fix tterm))
           ((unless (mbt (equal (tterm->kind tterm) :fncall))) nil))
        (tterm-list->var-judgements (tterm->args tterm))))

    (define tterm->var-judgements ((tterm tterm-p))
      :measure (list (tterm->expr-count tterm) 3 0)
      :returns (rv var-judgement-list-p)
      :flag term
      (b* ((tterm (tterm-fix tterm)))
        (case (tterm->kind tterm)
          (:quote nil)
          (:var (tterm-var->var-judgements tterm))
          (:if (tterm-if->var-judgements tterm))
          (:fncall (tterm-fncall->var-judgements tterm))))
      ///
      (verify-guards tterm->var-judgements)
      (fty::deffixequiv-mutual tterm->var-judgements))
    )
 )

(define tterm->smt-judgement ((tterm tterm-p))
  :returns (rv smt-judgement-p)
  (b* ((tterm (tterm-fix tterm)))
    (smt-judgement (std::mergesort (tterm->var-judgements tterm))
                   (std::mergesort (tterm->fn-judgements tterm))))
  ///
  (fty::deffixequiv tterm->smt-judgement))


(define tterm-list->unified-smt-judgement ((tterms tterm-list-p))
  :returns (rv smt-judgement-p)
  (b* ((tterms (tterm-list-fix tterms)))
    (smt-judgement (std::mergesort (tterm-list->var-judgements tterms))
                   (std::mergesort (tterm-list->fn-judgements tterms))))
  ///
  (fty::deffixequiv tterm-list->unified-smt-judgement))


(defsection tterm-type-extract-cp

  (define tterm-type-extract-cp ((cl pseudo-term-listp)
                                 (hint t)
                                 state)
    (b* (((unless (pseudo-term-listp cl)) (mv t nil state))
         ((unless (smtlink-hint-p hint)) (mv t nil state))
         ;; Parse tterms
         ((mv fail tterms) (tterm-parse-clause2 cl))
         ((if fail) (mv t nil state))
         ;; Single-term representation of clause terms
         (mono-expr (disjoin (tterm-list->expr-list tterms)))
         ;; Goal for next clause processor
         (next-expr (smt-judgement-clause
                      (tterm-list->unified-smt-judgement tterms)
                      mono-expr))
         (next-cp (cdr (assoc-equal 'tterm-type-extract
                                    *SMT-architecture*)))
         ((if (null next-cp)) (mv t nil state))
         (next-hint
           `(:clause-processor (,next-cp clause ',hint state)))
         (next-goal `((hint-please ',next-hint) ,next-expr))
         ;; Side condition
         (side-goal (list (implies-expr next-expr mono-expr))))
      (value (list next-goal
                   side-goal))))

  (defrule correctness-of-tterm-type-extract-cp
    (implies (and (pseudo-term-listp cl)
                  (alistp a)
                  (ev-smtcp
                    (conjoin-clauses
                      (acl2::clauses-result
                        (tterm-type-extract-cp cl hint state)))
                    a))
             (ev-smtcp (disjoin cl) a))
    :do-not-induct t
    :expand (tterm-type-extract-cp cl hint state)
    :in-theory (e/d (ev-and) (ev-smtcp-of-disjoin))
    :rule-classes :clause-processor)
  )
