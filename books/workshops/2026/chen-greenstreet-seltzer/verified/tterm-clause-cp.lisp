;; Copyright (C) 2015, University of British Columbia
;; Written by Mark Greenstreet and Chris Chen (2 Feb 2024)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "basics")
(include-book "tterm-clause")
(include-book "tterm-triv")
(include-book "type-options")
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


;; Define correctness properties for tterm-clause processors
(encapsulate
    (((tterm-trans-fn * * state) => *)
     ((tterm-map-fn * * state) => *)
     ((env-trans-fn *) => *)
     ((current-cp-fn) => *))

  (local
    (defun tterm-trans-fn (tterm opts state)
           (declare (ignore opts state))
           (tterm-fix tterm)))

  (local
    (defun tterm-map-fn (tterms opts state)
      (declare (xargs :measure (tterm-list-count tterms)))
      (b* ((tterms (tterm-list-fix tterms)))
        (if (consp tterms)
            (cons (tterm-trans-fn (car tterms) opts state)
                  (tterm-map-fn (cdr tterms) opts state))
          nil))))

  (local
    (defun env-trans-fn (a)
      a))

  (local
    (defun current-cp-fn ()
      'process-hint))

  (defrule symbolp-of-current-cp-fn
    (symbolp (current-cp-fn)))

  (defrule tterm-p-of-tterm-trans-fn
    (tterm-p (tterm-trans-fn tterm opts state)))

  (defrule tterm-trans-fn-preserves-expr-eval-backwards
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (alistp a)
                  (ev-smtcp (tterm->expr (tterm-trans-fn tterm opts state))
                            (env-trans-fn a)))
             (ev-smtcp (tterm->expr tterm) a)))

  (defrule tterm-trans-fn-preserves-correct-p-forwards
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (alistp a)
                  (tterm-correct-p tterm a))
             (tterm-correct-p (tterm-trans-fn tterm opts state)
                              (env-trans-fn a))))

  (defrule tterm-list-p-of-tterm-map-fn
    (tterm-list-p (tterm-map-fn tterms opts state)))

  (defrule tterm-map-fn-preserves-expr-eval-backwards
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (alistp a)
		  (tterm-list-p tterms)
		  (ev-smtcp (disjoin (tterm-list->expr-list
				       (tterm-map-fn tterms opts state)))
			    (env-trans-fn a)))
	     (ev-smtcp (disjoin (tterm-list->expr-list tterms)) a)))

  (defrule tterm-map-fn-preserves-correct-p-forwards
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (alistp a)
	          (tterm-list-p tterms)
                  (tterm-list-correct-p tterms a))
             (tterm-list-correct-p (tterm-map-fn tterms opts state)
				   (env-trans-fn a)))))


(define tterm-trans-fn-cp ((cl pseudo-term-listp)
                           (hint t)
                           state)
  (b* (((unless (pseudo-term-listp cl)) (mv t nil state))
       ((unless (smtlink-hint-p hint)) (mv t nil state))
       (goal (disjoin cl))
       ((mv fail tterm) (tterm-parse-clause goal))
       ((if fail) (mv t nil state))
       (next-cp (cdr (assoc-equal (current-cp-fn) *SMT-architecture*)))
       ((if (null next-cp)) (mv t nil state))
       (type-opt (construct-type-options hint goal))
       (new-tt (tterm-trans-fn tterm type-opt state))
       (the-hint
         `(:clause-processor (,next-cp clause ',hint state)))
       (new-cl (tterm-clause new-tt))
       (hinted-goal `((hint-please ',the-hint) ,new-cl)))
    (value (list hinted-goal))))


(defrule correctness-of-tterm-trans-fn-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                  (conjoin-clauses
                    (acl2::clauses-result
                      (tterm-trans-fn-cp cl hint state)))
                  (env-trans-fn a)))
           (ev-smtcp (disjoin cl) a))
  :do-not-induct t
  :expand (tterm-trans-fn-cp cl hint state)
  :in-theory (disable ev-smtcp-of-disjoin)
  :rule-classes :clause-processor)


(define tterm-map-fn-cp ((cl pseudo-term-listp)
                               (hint t)
                               state)
  (b* (((unless (pseudo-term-listp cl)) (mv t nil state))
       ((unless (smtlink-hint-p hint)) (mv t nil state))
       ((mv fail tterms) (tterm-parse-clause2 cl))
       ((if fail) (mv t nil state))
       (next-cp (cdr (assoc-equal (current-cp-fn) *SMT-architecture*)))
       ((if (null next-cp)) (mv t nil state))
       (type-opt (construct-type-options hint (disjoin cl)))
       (new-tts (tterm-map-fn tterms type-opt state))
       (the-hint
         `(:clause-processor (,next-cp clause ',hint state)))
       (new-cl (tterms->tterm-clauses new-tts))
       (hinted-goal `((hint-please ',the-hint) ,@new-cl)))
    (value (list hinted-goal))))


(defrule correctness-of-tterm-map-fn-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                  (conjoin-clauses
                    (acl2::clauses-result
                      (tterm-map-fn-cp cl hint state)))
                  (env-trans-fn a)))
           (ev-smtcp (disjoin cl) a))
  :do-not-induct t
  :expand (tterm-map-fn-cp cl hint state)
  :in-theory (disable ev-smtcp-of-disjoin)
  :rule-classes :clause-processor)


(define tterm-identity-cp ((cl pseudo-term-listp)
                           (hint t)
                           state)
  (b* (((unless (pseudo-term-listp cl)) (mv t nil state))
       ((unless (smtlink-hint-p hint)) (mv t nil state))
       (goal (disjoin cl))
       ((mv fail tterm)
        (prog2$ (cw "SMT-tterm-identity-cp goal: ~x0"
                    goal)
                (tterm-parse-clause goal)))
       ((if fail) (mv t nil state))
       (next-cp (cdr (assoc-equal 'tterm-identity *SMT-architecture*)))
       ((if (null next-cp)) (mv t nil state))
       (the-hint
         `(:clause-processor (,next-cp clause ',hint state)))
       (new-cl (tterm-clause tterm))
       (hinted-goal `((hint-please ',the-hint) ,new-cl)))
    (value (list hinted-goal))))


(defrule correctness-of-tterm-identity-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                  (conjoin-clauses
                    (acl2::clauses-result
                      (tterm-identity-cp cl hint state)))
                  a))
           (ev-smtcp (disjoin cl) a))
  :do-not-induct t
  :expand (tterm-identity-cp cl hint state)
  :in-theory (disable ev-smtcp-of-disjoin)
  :rule-classes :clause-processor)
