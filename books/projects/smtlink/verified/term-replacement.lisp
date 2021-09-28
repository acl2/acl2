;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (April 14th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "basics")
(include-book "evaluator")
(include-book "hint-interface")
(include-book "returns-judgement")
(include-book "replace-options")

(define replace-fixer ((term pseudo-termp)
                       (judgements pseudo-termp)
                       (path-cond pseudo-termp)
                       (fixer symbol-thm-spec-alist-p)
                       state)
  :guard (and (consp term)
              (symbolp (car term))
              (not (equal (car term) 'quote)))
  :returns (new-term pseudo-termp)
  (b* (((unless (mbt (and (pseudo-termp term)
                          (consp term)
                          (symbolp (car term))
                          (pseudo-termp judgements)
                          (pseudo-termp path-cond)
                          (symbol-thm-spec-alist-p fixer))))
        (pseudo-term-fix term))
       ((cons fn actuals) term)
       (fixer-pair (assoc-equal fn fixer))
       ((unless fixer-pair) term)
       (replace-spec (cdr fixer-pair))
       (substed-theorem (get-substed-theorem replace-spec actuals state))
       ((mv ok hypo concl)
        (get-hypotheses-and-conclusion substed-theorem fn actuals))
       ((unless ok)
        (prog2$ (er hard? 'term-replacement=>replace-fixer
                    "Malformed returns theorem ~p0.~%" substed-theorem)
                term))
       (ok1 (path-test-list `(if ,judgements ,path-cond 'nil) hypo))
       ((unless ok1) term)
       ((mv ok2 rhs)
        (case-match concl
          (('equal !term rhs) (mv t rhs))
          (& (mv nil nil))))
       ((unless (and ok2
                     ;; (implies (consp rhs) (not (equal (car rhs) 'quote)))
                     ))
        (prog2$ (er hard? 'term-replacement=>replace-fixer
                    "Malformed conclusion ~p0.~%" concl)
                term)))
    rhs))

(defthm correctness-of-replace-fixer
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp term)
                (and (consp term)
                     (symbolp (car term))
                     (not (equal (car term) 'quote)))
                (pseudo-termp judgements)
                (pseudo-termp path-cond)
                (symbol-thm-spec-alist-p fixer)
                (alistp a)
                (ev-smtcp judgements a)
                (ev-smtcp path-cond a))
           (equal
            (ev-smtcp term a)
            (ev-smtcp (replace-fixer term judgements path-cond fixer state)
                      a)))
  :hints (("Goal"
           :in-theory (e/d () (pseudo-termp
                               symbol-listp
                               consp-of-pseudo-lambdap
                               pseudo-term-listp-of-symbol-listp
                               pseudo-term-listp-of-cdr-of-pseudo-termp
                               acl2::symbolp-of-car-when-symbol-listp
                               acl2::symbol-listp-of-cdr-when-symbol-listp
                               acl2::pseudo-termp-cadr-from-pseudo-term-listp
                               assoc-equal
                               correctness-of-get-substed-theorem
                               correctness-of-get-hypotheses-and-conclusion))
           :expand (replace-fixer term judgements path-cond fixer state)
           :use ((:instance correctness-of-get-substed-theorem
                            (actuals (cdr term))
                            (respec (cdr (assoc-equal (car term) fixer))))
                 (:instance correctness-of-get-hypotheses-and-conclusion
                            (thm (get-substed-theorem
                                  (cdr (assoc-equal (car term) fixer))
                                  (cdr term)
                                  state))
                            (fn (car term))
                            (actuals (cdr term))
                            (a a))))))

(defines replace-term
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil
  :returns-hints (("Goal"
                   :in-theory (e/d (good-typed-term-list-p)
                                   (pseudo-termp
                                    acl2-count
                                    lambda-of-pseudo-lambdap
                                    symbol-listp))))

  (define replace-fncall ((tterm typed-term-p)
                          (options replace-options-p)
                          state)
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'fncallp))
    :returns (new-tt good-typed-term-p)
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (replace-options-p options)
                            (equal (typed-term->kind tterm) 'fncallp)
                            (good-typed-term-p tterm))))
          (make-typed-term))
         ((replace-options ro) options)
         ((typed-term tt) tterm)
         ((typed-term tt-top) (typed-term->top tt))
         (tt-actuals (typed-term-fncall->actuals tt))
         (new-actuals (replace-term-list tt-actuals options state))
         (new-tta.term-lst (typed-term-list->term-lst new-actuals))
         (new-tta.judgements (typed-term-list->judgements new-actuals))
         ((cons fn &) tt.term)
         (new-term1 `(,fn ,@new-tta.term-lst))
         (new-term2 (replace-fixer new-term1 new-tta.judgements
                                  tt.path-cond ro.fixers state))
         (new-top-judge (generate-judge-from-equality tt-top.term new-term2
                                                      tt-top.judgements
                                                      ro.supertype))
         (new-top (change-typed-term tt-top
                                     :term new-term2
                                     :judgements new-top-judge))
         ((unless (make-typed-fncall-guard new-top new-actuals)) tt))
      (make-typed-fncall new-top new-actuals)))

  (define replace-if ((tterm typed-term-p)
                      (options replace-options-p)
                      state)
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'ifp))
    :returns (new-tt good-typed-term-p)
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (replace-options-p options)
                            (equal (typed-term->kind tterm) 'ifp)
                            (good-typed-term-p tterm))))
          (make-typed-term))
         ((replace-options ro) options)
         ((typed-term tt) tterm)
         ((typed-term tt-cond) (typed-term-if->cond tt))
         ((typed-term tt-then) (typed-term-if->then tt))
         ((typed-term tt-else) (typed-term-if->else tt))
         ((typed-term tt-top) (typed-term->top tt))
         (new-cond (replace-term tt-cond options state))
         ((typed-term new-ttc) new-cond)
         (new-then (replace-term tt-then options state))
         ((typed-term new-ttt) new-then)
         (new-else (replace-term tt-else options state))
         ((typed-term new-tte) new-else)
         (new-term `(if ,new-ttc.term ,new-ttt.term ,new-tte.term))
         (new-top-judge (generate-judge-from-equality tt-top.term new-term
                                                      tt-top.judgements
                                                      ro.supertype))
         (new-top (change-typed-term tt-top
                                     :term new-term
                                     :judgements new-top-judge)))
      (make-typed-if new-top new-cond new-then new-else)))

  (define replace-term ((tterm typed-term-p)
                        (options replace-options-p)
                        state)
    :guard (good-typed-term-p tterm)
    :returns (new-tt good-typed-term-p)
    :measure (list (acl2-count (typed-term->term tterm)) 1)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (good-typed-term-p tterm)
                            (replace-options-p options))))
          (make-typed-term))
         ((if (equal (typed-term->kind tterm) 'variablep)) tterm)
         ((if (equal (typed-term->kind tterm) 'quotep)) tterm)
         ((if (equal (typed-term->kind tterm) 'ifp))
          (replace-if tterm options state))
         ((if (equal (typed-term->kind tterm) 'fncallp))
          (replace-fncall tterm options state)))
      (prog2$ (er hard? 'term-replacement=>replace-term
                  "Found lambda term in goal.~%")
              tterm)))

  (define replace-term-list ((tterm-lst typed-term-list-p)
                             (options replace-options-p)
                             state)
    :returns (new-ttl good-typed-term-list-p)
    :guard (good-typed-term-list-p tterm-lst)
    :measure (list (acl2-count (typed-term-list->term-lst tterm-lst)) 1)
    (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                            (good-typed-term-list-p tterm-lst)
                            (replace-options-p options))))
          nil)
         ((unless (consp tterm-lst)) nil)
         ((cons tterm-hd tterm-tl) tterm-lst)
         (tt-car (replace-term tterm-hd options state))
         (tt-cdr (replace-term-list tterm-tl options state))
         ((unless (implies (consp tt-cdr)
                           (equal (typed-term->path-cond tt-car)
                                  (typed-term-list->path-cond tt-cdr))))
          tterm-lst))
      (cons tt-car tt-cdr)))
)

(verify-guards replace-term)

(define term-replacement-fn ((cl pseudo-term-listp)
                             (smtlink-hint t)
                             state)
  :returns (subgoal-lst pseudo-term-list-listp)
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint)) (list cl))
       (goal (disjoin cl))
       (h (construct-replace-options smtlink-hint))
       ((mv okp tterm)
        (case-match goal
          (('implies judges term)
           (mv t (make-typed-term :term term
                                  :path-cond ''t
                                  :judgements judges)))
          (& (mv nil (make-typed-term)))))
       ((unless okp)
        (prog2$ (er hard? 'term-replacement=>term-replacement-fn
                    "The input term is of wrong shape. It should look like ~
                     (typed-goal ...) ~%")
                (list cl)))
       ((unless (good-typed-term-p tterm))
        (prog2$ (er hard? 'term-replacement=>term-replacement-fn
                    "Not a good-typed-term-p: ~q0" tterm)
                (list cl)))
       (replaced-tterm (replace-term tterm h state))
       (replaced-judgements (typed-term->judgements replaced-tterm))
       (replaced-term (typed-term->term replaced-tterm))
       (new-cl `((implies ,replaced-judgements ,replaced-term)))
       (next-cp (cdr (assoc-equal 'term-replacement *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',smtlink-hint state)))
       (hinted-goal `((hint-please ',the-hint) ,@new-cl)))
    (list hinted-goal)))

(define term-replacement-cp ((cl pseudo-term-listp)
                             (hints t)
                             state)
  (b* ((new-clause (term-replacement-fn cl hints state)))
    (value new-clause)))

;; (defthm correctness-of-type-replacement-cp
;;   (implies (and (ev-smtcp-meta-extract-global-facts)
;;                 (pseudo-term-listp cl)
;;                 (alistp a)
;;                 (ev-smtcp
;;                  (conjoin-clauses
;;                   (acl2::clauses-result
;;                    (term-replacement-cp cl hint state)))
;;                  a))
;;            (ev-smtcp (disjoin cl) a))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :in-theory (enable term-replacement-cp
;;                               term-replacement-fn))))
