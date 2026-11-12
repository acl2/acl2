;; Copyright (C) 2015, University of British Columbia
;; Written by Mark Greenstreet and Chris Chen (2 Feb 2024)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "tterm")
(include-book "std/util/defprojection" :dir :system)

(set-state-ok t)
(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))


(local (in-theory (e/d
  ()
  (pseudo-termp pseudo-term-listp symbol-listp  ; Mark is impatient
   boolean-listp member-equal consp-of-pseudo-lambdap
   pseudo-lambdap-of-fn-call-of-pseudo-termp lambda-of-pseudo-lambdap
   default-car
   (:type-prescription pseudo-lambdap)))))


; tterm-clause: produce an ACL2 clause corresponding to tterm
; This version constructs an expression with 'implies' and 'if' where the
; if-expression is a "translated" and.  We might want to just create the
; clause directly:
; (list ,(not (tterm-p (quote ,tterm)))
;       ,(not ,(tterm-correct-expr tterm))
;       ,(tterm->expr tterm))
; But I'm leaving it in the current form for now to be close to Yan's
; representation.  The big difference between tterm-clause and what Yan
; does is that I'm including tterm in the goal so the next clause processor
; can recover it.

(define tterm-clause ((tterm tterm-p))
  :returns (cl pseudo-termp :hints(("Goal" :in-theory (enable pseudo-termp))))
  (b* ((tterm (tterm-fix tterm)))
    `(implies
       (if (acl2::any-p$inline (quote ,tterm))
           ,(tterm-correct-expr tterm)
         ''nil)
       ,(tterm->expr tterm)))
  ///
  (defrule eval-tterm-clause-if-eval-tterm-expr
    (implies (ev-smtcp (tterm->expr tterm) a)
             (ev-smtcp (tterm-clause tterm) a))))


; (tterm-parse-clause cl) -> (mv fail tterm)
;   cl should be the pseudo-termp returned by (disjoin clause) where clause
;     is a list of disjuncts, where each disjunct satisfies termp.
;   If cl has the form of a clause constructed by (tterm-clause tterm),
;     tterm-parse-clause returns (mv nil tterm).
;     In this case, we ensure (see tterm-parse-clause-when-good-cl) that
;       for any context, a, either (tterm-correct-p tterm a) holds or cl
;       is vacously satisified, e.g. a type-hypotheses of cl is violated
;       in context a.  We also ensure that (tterm->expr tterm) implies
;       cl in any context a.
;   Otherwise cl does not have the form of a clause constructed by
;     (tterm-clause tterm), and (tterm-parse-clause cl) reutrns (mv fail tterm)
;     where fail is not nil, and tterm satisfies tterm-p (to make guard and
;     returns theorems happy.  The current implementation returns t for
;     fail in this case.
;     TODO: write smt:fail((info acl2::any-p)) -> nil.  Then, we can
;     return clauses that will fail, but the info argument will give
;     potentially useful feedback to the user.

(define tterm-parse-clause ((cl pseudo-termp))
  :returns (mv (fail booleanp) (tterm tterm-p))
  (b* (((unless (pseudo-termp cl)) (mv t (make-tterm)))
       (tterm (case-match cl
		      (('implies ('if ('acl2::any-p$inline ('quote tterm)) & &) &) tterm)
		      (& nil)))
       ((unless (and (tterm-p tterm)
		     (equal (tterm-clause tterm) cl)))
	(mv t (make-tterm))))
    (mv nil tterm))
  ///
  (defrule tterm-parse-clause-of-tterm-clause
    (implies (tterm-p tterm)
             (mv-let
                 (fail parsed-tterm)
                 (tterm-parse-clause (tterm-clause tterm))
               (and (not fail)
                    (equal parsed-tterm tterm))))
    :expand ((tterm-clause tterm))
    :in-theory (enable pseudo-termp))

  (defrule tterm-parse-clause-pass
    (mv-let
        (fail tterm)
        (tterm-parse-clause cl)
      (implies (and (not fail)
                    (ev-smtcp (tterm->expr tterm) a))
               (ev-smtcp cl a)))
    :in-theory (disable eval-tterm-clause-if-eval-tterm-expr)
    :use (:instance eval-tterm-clause-if-eval-tterm-expr
                    (tterm (mv-nth 1 (tterm-parse-clause cl))))))


;; Lift evaluation of tterm-clauses to evaluation of their components
(encapsulate ()
  (local
    (acl2::defruled tterm-clause-of-tterm-parse-clause
      (mv-let (fail parsed-tterm)
              (tterm-parse-clause cl)
        (implies (not fail)
                 (equal (tterm-clause parsed-tterm)
                        cl)))
      :expand ((tterm-parse-clause cl))))

  (local
    (acl2::defruled ev-smtcp-tterm-clause-equivalent
      (mv-let (fail tterm)
              (tterm-parse-clause cl)
        (implies (not fail)
                 (equal (ev-smtcp cl a)
                        (ev-smtcp (tterm-clause tterm) a))))
      :in-theory (enable tterm-clause-of-tterm-parse-clause)))

  (defrule ev-smtcp-of-tterm-parse-clause
    (mv-let (fail tterm)
            (tterm-parse-clause cl)
      (implies (not fail)
               (equal (ev-smtcp cl a)
                      (implies (tterm-correct-p tterm a)
                               (ev-smtcp (tterm->expr tterm) a)))))
    :in-theory (e/d (tterm-clause
                     ev-smtcp-tterm-clause-equivalent)
                    (tterm-parse-clause-of-tterm-clause))))


(std::defprojection tterms->tterm-clauses ((x tterm-list-p))
  :returns (rv pseudo-term-listp)
  (tterm-clause x)
  ///
  (defrule eval-disjoin-tterm-clauses-implies-disjoin-tterm-expr-list
    (implies (and (tterm-list-p tterms)
                  (tterm-list-correct-p tterms a)
                  (ev-smtcp (disjoin (tterms->tterm-clauses tterms)) a))
             (ev-smtcp (disjoin (tterm-list->expr-list tterms)) a))
    :hints (("Goal" :induct (len tterms))))
  (defrule eval-disjoin-tterm-expr-list-implies-eval-disjoin-tterm-clauses
    (implies (ev-smtcp (disjoin (tterm-list->expr-list tterms)) a)
             (ev-smtcp (disjoin (tterms->tterm-clauses tterms)) a))
    :hints (("Goal" :induct (len tterms)))))

; (tterm-parse-clause2 cl) -> (mv fail tterm)
(define tterm-parse-clause2 ((cl pseudo-term-listp))
  :returns (mv (fail booleanp) (tterm tterm-list-p))
  (b* (((unless (pseudo-term-listp cl)) (mv t (list (make-tterm))))
       ((unless (consp cl)) (mv nil nil))
       ((mv fail head-tterm) (tterm-parse-clause (car cl)))
       ((if fail) (mv t (list (make-tterm))))
       ((mv fail tail-tterms) (tterm-parse-clause2 (cdr cl)))
       ((if fail) (mv t (list (make-tterm)))))
    (mv nil (cons head-tterm tail-tterms)))
  ///
  (defrule tterm-parse-clause2-of-tterms->tterm-clauses
    (implies (tterm-list-p tterms)
             (mv-let
                 (fail parsed-tterms)
                 (tterm-parse-clause2 (tterms->tterm-clauses tterms))
               (and (not fail)
                    (equal parsed-tterms tterms))))
    :induct (len tterms))
  ;; (defrule tterm-parse2-clause-pass
  ;;   (mv-let
  ;;       (fail tterms)
  ;;       (tterm-parse-clause2 cl)
  ;;     (implies (and (not fail)
  ;;       	    (ev-smtcp (disjoin (tterm-list->expr-list tterms))
  ;;       		      a))
  ;;              (ev-smtcp (disjoin cl) a)))
  ;;   :in-theory (disable ev-smtcp-of-disjoin))
  (defrule ev-smtcp-of-tterm-parse-clause2
    (mv-let (fail tterms)
            (tterm-parse-clause2 cl)
      (implies (not fail)
               (equal (ev-smtcp (disjoin cl) a)
                      (implies (tterm-list-correct-p tterms a)
                               (ev-smtcp (disjoin (tterm-list->expr-list
                                                    tterms)) a)))))
    :expand (disjoin cl)
    :in-theory (disable ev-smtcp-of-disjoin)))
