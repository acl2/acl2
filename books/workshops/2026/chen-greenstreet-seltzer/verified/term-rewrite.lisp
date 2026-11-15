;; Copyright (C) 2026, University of British Columbia
;; Written by Chris Chen
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

;;
;; This book defines a computed hints and clause processors that
;; apply rewrite$ to smtlink typed terms.

(in-package "SMT")
(include-book "hints/hint-wrapper" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "tools/rewrite-dollar" :dir :system)
(include-book "xdoc/top" :dir :system)

(include-book "basics")
(include-book "hint-interface")
(include-book "tterm-clause")

(set-state-ok t)
(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))

(local (in-theory (e/d
  (ev-smtcp-of-fncall-args)
  (pseudo-termp pseudo-term-listp symbol-listp  ; Mark is impatient
   boolean-listp member-equal consp-of-pseudo-lambdap
   pseudo-lambdap-of-fn-call-of-pseudo-termp lambda-of-pseudo-lambdap
   default-car
   (:type-prescription pseudo-lambdap)))))

(defsection SMT-term-rewrite
  :parents (verified)

  (program)

  (define rewrite$-helper-fn (term hyps theory fuel state)
    (b* (((if (zp fuel))
          (prog2$ (cw "rewrite$-helper reached limit of ~x0 applications~%"
                      (rewrite-stack-limit (w state)))
                  (mv t nil state)))
         ((mv rewrite-fail result state)
          (acl2::rewrite$ term
                          :hands-off '(not)
                          :hyps hyps
                          :in-theory theory))
         ((if rewrite-fail)
          (prog2$ (cw "rewrite$-helper failed for ~x0 ~x1~%"
                      term hyps)
                  (mv t nil state)))
         ((list new-term & &) result)
         ((if (equal term new-term)) (value new-term)))
      (rewrite$-helper-fn new-term hyps theory (1- fuel) state)))

  (define rewrite$-helper (term hyps theory state)
    (b* ((fuel (acl2::rewrite-stack-limit (w state)))
         ((unless (and (pseudo-termp term)
                       (pseudo-term-listp hyps)
                       (pseudo-termp theory)
                       (state-p state)
                       (natp fuel)))
          (mv t nil state)))
      (rewrite$-helper-fn term hyps theory fuel state)))

  (define tterm-rewrite$-map (tterms theory state)
    (b* (((unless (and (tterm-list-p tterms)
                       (pseudo-termp theory)
                       (state-p state)))
          (mv t nil state))
         ((unless (consp tterms)) (value nil))
         ;; Simplify correctness condition
         (head-correct-expr (tterm-correct-smt-expr (car tterms)))
         ((mv fail hypo state) (rewrite$-helper head-correct-expr
                                                nil
                                                theory
                                                state))
         ((if fail) (mv t nil state))
         ;; Rewrite expression
         (head-expr (tterm->expr (car tterms)))
         ((mv fail new-head state) (rewrite$-helper head-expr
                                                    (list hypo)
                                                    theory
                                                    state))
         ((if fail) (mv t nil state))
         ((mv fail new-tail state) (tterm-rewrite$-map (cdr tterms)
                                                       theory
                                                       state))
         ((if fail) (mv t nil state)))
      (value (cons new-head new-tail))))

  (define SMT-term-rewrite-hint (cl kwd-alist state)
    :guard-debug t
    :parents (SMT-computed-hints)
    :short "@('SMT::SMT-term-rewrite-hint') WRITE SOMETHING."
    (b* (((unless (and (pseudo-term-listp cl)
                       (consp kwd-alist)
                       (consp (cdr kwd-alist))
                       (consp (cadr kwd-alist))
                       (= (len (cadr kwd-alist))
                          4)
                       (state-p state)))
          (prog2$ (cw "SMT-term-rewrite-hint: preconditions not met~%")
                  (value nil)))
         ((list* cp-kwd (list next-cp & q-smt-hint &) kwd-alist-tail) kwd-alist)
         ((unless (equal cp-kwd :clause-processor))
          (prog2$ (cw "SMT-term-rewrite-hint: missing clause processor in kwd-alist: ~x0~%"
                      kwd-alist)
                  (value nil)))
         ((unless (and (quotep q-smt-hint)
                       (smtlink-hint-p (unquote q-smt-hint))))
          (prog2$ (cw "not quoted smtlink-hint-p: ~x0~%" q-smt-hint)
                  (value nil)))
         (smt-hint (unquote q-smt-hint))
         (translation-theory (smtlink-hint->translation-theory smt-hint))
         ;; Clause rewriting follows
         ((mv fail tterms) (tterm-parse-clause2 cl))
         ((if fail) (prog2$ (cw "not a list of tterm-clauses: ~x0~%" tterms)
                            (value nil)))
         ((mv fail new-exprs state)
          (tterm-rewrite$-map tterms translation-theory state))
         ((if fail) (value nil)))
      (value `(:computed-hint-replacement ((SMT-computed-hint clause))
               :clause-processor (,next-cp clause ',(cons smt-hint new-exprs) state)
               ,@kwd-alist-tail))))

  (logic)


  (define tterms-exprs->side-goals ((original-tts tterm-list-p)
                                    (new-exprs pseudo-term-listp)
                                    (trans-theory pseudo-termp))
    :measure (+ (len (tterm-list-fix original-tts))
                (len (pseudo-term-list-fix new-exprs)))
    :returns (side-goals true-listp)
    (b* ((original-tts (tterm-list-fix original-tts))
         (new-exprs (pseudo-term-list-fix new-exprs))
         (trans-theory (pseudo-term-fix trans-theory))
         ((unless (and (consp original-tts)
		       (consp new-exprs)))
	  nil)
         (original-tt (car original-tts))
         (original-expr (tterm->expr original-tt))
         (new-expr (car new-exprs))
         (original-correct-expr (tterm-correct-expr original-tt))
         (side-condition (implies-expr original-correct-expr
				       (equal-expr original-expr
                                                   new-expr)))
         (side-hint `(acl2::hint-wrapper
		       '(:in-theory ,trans-theory)))
         (side-goal `((not ,side-hint)
		      ,side-condition)))
      (cons side-goal
	    (tterms-exprs->side-goals (cdr original-tts)
				      (cdr new-exprs)
				      trans-theory)))
    ///
    (local
     (acl2::defruled correctness-of-side-condition
       (implies (and (tterm-correct-p tt a)
		     (ev-smtcp (implies-expr (tterm-correct-expr tt)
					     (equal-expr (tterm->expr tt)
							 new-expr))
			       a))
		(iff (ev-smtcp (tterm->expr tt) a)
		     (ev-smtcp new-expr a)))
       :in-theory (enable equal-expr
			  implies-expr)))
    (local
     (acl2::defruled tterms-exprs-correctness-base-case-0
       (implies (and (pseudo-term-listp new-exprs)
		     (equal 0 (len new-exprs)))
		(not (acl2::or-list (ev-smtcp-lst new-exprs a))))))

    (local
     (acl2::defruled tterms-exprs-correctness-base-case-1
       (implies
	 (and (tterm-list-p original-tts)
	      (tterm-list-correct-p original-tts a)
	      (equal (len original-tts) 0))
	 (not (acl2::or-list (ev-smtcp-lst
                               (tterm-list->expr-list original-tts)
			       a))))))

    (defrule correctness-of-tterms-exprs->side-goals
	  (implies (and (tterm-list-p original-tts)
			(tterm-list-correct-p original-tts a)
			(pseudo-term-listp new-exprs)
			(equal (len original-tts)
			       (len new-exprs))
			(ev-smtcp (conjoin-clauses
				   (tterms-exprs->side-goals
				    original-tts
				    new-exprs
				    trans-theory))
	                          a))
		   (iff (ev-smtcp (disjoin (tterm-list->expr-list original-tts))
				  a)
			(ev-smtcp (disjoin new-exprs) a)))
	  :in-theory (enable correctness-of-side-condition
                             tterms-exprs-correctness-base-case-0
			     tterms-exprs-correctness-base-case-1)))


  ;; Clause processors
  ;; If rewritten clauses = original tterm-list->expr-list, continue to next
  ;; clause processor.
  ;; If the clause changed, reinject after 'process-hint
  ;; Discharge equality side condition with hint from translation-theory
  (define term-rewrite-cp ((cl pseudo-term-listp)
                           (hint t)
                           state)
    (b* (((unless (pseudo-term-listp cl)) (mv t nil state))
         ((unless (consp hint)) (mv t nil state))
         ((cons smt-hint new-cl) hint)
         ((unless (smtlink-hint-p smt-hint)) (mv t nil state))
         ((unless (pseudo-term-listp new-cl)) (mv t nil state))
         ((mv fail tterms) (tterm-parse-clause2 cl))
         ((if fail) (mv t nil state))
         ((unless (= (len new-cl) (len tterms)))
          (mv t nil state))
         (orig-exprs (tterm-list->expr-list tterms)))
      (if (equal orig-exprs new-cl)
          (b* ((next-cp (cdr (assoc-equal 'term-rewrite
                                          *SMT-architecture*)))
               ((if (null next-cp)) (mv t nil state))
               (the-hint
                 `(:clause-processor (,next-cp clause ',smt-hint
                                               state)))
               (hinted-goal `((hint-please ',the-hint) ,@cl)))
            (value (list hinted-goal)))
        (b* ((next-cp (cdr (assoc-equal 'process-hint
                                        *SMT-architecture*)))
             ((if (null next-cp)) (mv t nil state))
             (the-hint
               `(:clause-processor (,next-cp clause ',smt-hint state)))
             ;; New goals and side conditions
             (trans-theory (smtlink-hint->translation-theory smt-hint))
             (side-goals
               (tterms-exprs->side-goals tterms
                                         new-cl
                                         trans-theory))
             (hinted-new-goal `((hint-please ',the-hint) ,@new-cl)))
          (value (cons hinted-new-goal side-goals))))))


  (defrule correctness-of-term-rewrite-cp
    (implies (and (pseudo-term-listp cl)
                  (alistp a)
                  (ev-smtcp
                    (conjoin-clauses
                      (acl2::clauses-result
                        (term-rewrite-cp cl hint state)))
                    a))
             (ev-smtcp (disjoin cl) a))
    :do-not-induct t
    :expand (term-rewrite-cp cl hint state)
    :in-theory (disable ev-smtcp-of-disjoin)
    :rule-classes :clause-processor)
  )
