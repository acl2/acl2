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
(include-book "type-inference-bottomup")
(include-book "type-inference-topdown")
(include-book "replace-options")

(local (in-theory (disable (:executable-counterpart typed-term)
                           pseudo-termp pseudo-term-listp)))

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
       ((unless ok2)
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
                          (replace-options replace-options-p)
                          (type-options type-options-p)
                          (clock natp)
                          state)
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'fncallp))
    :returns (new-tt good-typed-term-p)
    :measure (list (nfix clock) (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (replace-options-p replace-options)
                            (type-options-p type-options)
                            (equal (typed-term->kind tterm) 'fncallp)
                            (good-typed-term-p tterm)
                            (natp clock))))
          (make-typed-term))
         ((if (zp clock)) tterm)
         (- (cw "fncall tterm: ~q0" tterm))
         ((replace-options ro) replace-options)
         ((type-options to) type-options)
         ((typed-term tt) tterm)
         ((typed-term tt-top) (typed-term->top tt))
         (tt-actuals (typed-term-fncall->actuals tt))
         (tta.judgements (typed-term-list->judgements tt-actuals))
         (term1 (replace-fixer tt.term tta.judgements
                               tt.path-cond ro.fixers state))
         ((if (equal term1 tt.term))
          (b* (((cons fn &) tt.term)
               (tt1-actuals (replace-term-list tt-actuals ro to clock state))
               (tt1a.term-lst (typed-term-list->term-lst tt1-actuals))
               (term1 `(,fn ,@tt1a.term-lst))
               (- (cw "term1: ~q0" term1))
               (tt1-judge-top (generate-judge-from-equality tt-top.term term1
                                                            tt-top.judgements
                                                            ro.supertype))
               (- (cw "tt1-judge-top: ~q0" tt1-judge-top))
               (tt1-top (change-typed-term tt-top
                                           :term term1
                                           :judgements tt1-judge-top))
               (- (cw "tt1-top: ~q0" tt1-top))
               ((unless (make-typed-fncall-guard tt1-top tt1-actuals)) tt))
            (make-typed-fncall tt1-top tt1-actuals)))
         (- (cw "term1: ~q0" term1))
         (judge1 (type-judgement term1 tt.path-cond to to.names
                                 state))
         (- (cw "judge1: ~q0" judge1))
         (tt1 (make-typed-term :term term1
                               :path-cond tt.path-cond
                               :judgements judge1))
         ((unless (good-typed-term-p tt1)) tt)
         (- (cw "tt1: ~q0" tt1))
         (expected (generate-judge-from-equality tt-top.term term1
                                                 tt-top.judgements
                                                 ro.supertype))
         (- (cw "expected: ~q0" expected))
         (tt1-unified (unify-type tt1 expected to state))
         (- (cw "tt1-unified: ~q0" tt1-unified)))
      (replace-term tt1-unified ro to (1- clock) state)))

  (define replace-if ((tterm typed-term-p)
                      (replace-options replace-options-p)
                      (type-options type-options-p)
                      (clock natp)
                      state)
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'ifp))
    :returns (new-tt good-typed-term-p)
    :measure (list (nfix clock) (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (replace-options-p replace-options)
                            (type-options-p type-options)
                            (equal (typed-term->kind tterm) 'ifp)
                            (good-typed-term-p tterm)
                            (natp clock))))
          (make-typed-term))
         ((replace-options ro) replace-options)
         ((typed-term tt) tterm)
         ((typed-term tt-cond) (typed-term-if->cond tt))
         ((typed-term tt-then) (typed-term-if->then tt))
         ((typed-term tt-else) (typed-term-if->else tt))
         ((typed-term tt-top) (typed-term->top tt))
         ;; BOZO: we need to handle the replacement in condition
         ;; (new-cond (replace-term tt-cond options state))
         (new-cond tt-cond)
         ((typed-term new-ttc) new-cond)
         (new-then (replace-term tt-then ro type-options clock state))
         ((typed-term new-ttt) new-then)
         (new-else (replace-term tt-else ro type-options clock state))
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
                        (replace-options replace-options-p)
                        (type-options type-options-p)
                        (clock natp)
                        state)
    :guard (good-typed-term-p tterm)
    :returns (new-tt good-typed-term-p)
    :measure (list (nfix clock) (acl2-count (typed-term->term tterm)) 1)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (good-typed-term-p tterm)
                            (replace-options-p replace-options)
                            (type-options-p type-options)
                            (natp clock))))
          (make-typed-term))
         (- (cw "tterm: ~q0" tterm))
         ((if (equal (typed-term->kind tterm) 'variablep)) tterm)
         ((if (equal (typed-term->kind tterm) 'quotep)) tterm)
         ((if (equal (typed-term->kind tterm) 'ifp))
          (replace-if tterm replace-options type-options clock state))
         ((if (equal (typed-term->kind tterm) 'fncallp))
          (replace-fncall tterm replace-options type-options clock state)))
      (prog2$ (er hard? 'term-replacement=>replace-term
                  "Found lambda term in goal.~%")
              tterm)))

  (define replace-term-list ((tterm-lst typed-term-list-p)
                             (replace-options replace-options-p)
                             (type-options type-options-p)
                             (clock natp)
                             state)
    :returns (new-ttl good-typed-term-list-p)
    :guard (good-typed-term-list-p tterm-lst)
    :measure (list (nfix clock) (acl2-count (typed-term-list->term-lst tterm-lst)) 1)
    (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                            (good-typed-term-list-p tterm-lst)
                            (replace-options-p replace-options)
                            (type-options-p type-options)
                            (natp clock))))
          nil)
         ((unless (consp tterm-lst)) nil)
         ((cons tterm-hd tterm-tl) tterm-lst)
         (tt-car (replace-term tterm-hd replace-options type-options clock state))
         (tt-cdr (replace-term-list tterm-tl replace-options type-options clock
                             state))
         ((unless (implies (consp tt-cdr)
                           (equal (typed-term->path-cond tt-car)
                                  (typed-term-list->path-cond tt-cdr))))
          tterm-lst))
      (cons tt-car tt-cdr)))
  ///
  (defthm typed-term-of-replace-fncall
    (typed-term-p (replace-fncall tterm replace-options type-options clock state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (replace-fncall tterm replace-options
                                               type-options clock state)))))))
  (defthm typed-term-of-replace-if
    (typed-term-p (replace-if tterm replace-options type-options clock state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (replace-if tterm replace-options type-options
                                           clock state)))))))
  (defthm typed-term-of-replace-term
    (typed-term-p (replace-term tterm replace-options type-options clock state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (replace-term tterm replace-options type-options
                                             clock state)))))))
  (defthm typed-term-list-of-replace-term-list
    (typed-term-list-p
     (replace-term-list tterm-lst replace-options type-options clock state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-list-implies-typed-term-list)
             :use ((:instance good-typed-term-list-implies-typed-term-list
                              (tterm-lst
                               (replace-term-list tterm-lst replace-options
                                                  type-options clock state)))))))
  )

(verify-guards replace-term)

(skip-proofs
(defthm-replace-term-flag
  (defthm replace-if-maintains-path-cond
    (implies (and (replace-options-p replace-options)
                  (type-options-p type-options)
                  (equal (typed-term->kind tterm) 'ifp)
                  (good-typed-term-p tterm))
             (equal (typed-term->path-cond
                     (replace-if tterm replace-options type-options clock state))
                    (typed-term->path-cond tterm)))
    :flag replace-if
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d ()
                                   (pseudo-termp
                                    symbol-listp
                                    acl2::symbol-listp-when-not-consp
                                    consp-of-is-conjunct?
                                    acl2::pseudo-termp-cadr-from-pseudo-term-listp
                                    acl2::symbolp-of-car-when-symbol-listp
                                    pseudo-term-listp-of-symbol-listp
                                    acl2::pseudo-termp-opener))
                              :expand (replace-if tterm replace-options
                                                  type-options clock state)))))
  (defthm replace-fncall-maintains-path-cond
    (implies (and (replace-options-p replace-options)
                  (type-options-p type-options)
                  (equal (typed-term->kind tterm) 'fncallp)
                  (good-typed-term-p tterm))
             (equal (typed-term->path-cond
                     (replace-fncall tterm replace-options type-options clock state))
                    (typed-term->path-cond tterm)))
    :flag replace-fncall
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d ()
                                   (pseudo-termp
                                    symbol-listp
                                    acl2::symbol-listp-when-not-consp
                                    consp-of-is-conjunct?
                                    acl2::pseudo-termp-cadr-from-pseudo-term-listp
                                    acl2::symbolp-of-car-when-symbol-listp
                                    pseudo-term-listp-of-symbol-listp
                                    acl2::pseudo-termp-opener))
                   :expand (replace-fncall tterm replace-options type-options
                                           clock state)))))
  (defthm replace-term-maintains-path-cond
    (implies (and (replace-options-p options)
                  (type-options-p type-options)
                  (good-typed-term-p tterm))
             (equal (typed-term->path-cond
                     (replace-term tterm replace-options type-options clock state))
                    (typed-term->path-cond tterm)))
    :flag replace-term
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () ())
                   :expand (replace-term tterm replace-options type-options
                                         clock state)))))
  (defthm replace-term-list-maintains-path-cond
    (implies (and (replace-options-p options)
                  (type-options-p type-options)
                  (good-typed-term-list-p tterm-lst))
             (equal (typed-term-list->path-cond
                     (replace-term-list tterm-lst replace-options type-options
                                        clock state))
                    (typed-term-list->path-cond tterm-lst)))
    :flag replace-term-list
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (typed-term-list->path-cond)
                                   (pseudo-termp
                                    acl2::symbol-listp-when-not-consp
                                    consp-of-is-conjunct?
                                    acl2::pseudo-termp-cadr-from-pseudo-term-listp
                                    acl2::symbolp-of-car-when-symbol-listp
                                    pseudo-term-listp-of-symbol-listp
                                    acl2::pseudo-termp-opener
                                    pseudo-term-listp-of-symbol-listp))
                   :expand
                   ((replace-term-list tterm-lst replace-options type-options
                                       clock state)
                    (replace-term-list nil replace-options type-options clock
                                       state))))))
  :hints(("Goal"
          :in-theory (disable pseudo-termp
                              correctness-of-path-test-list
                              symbol-listp
                              correctness-of-path-test
                              acl2::symbol-listp-when-not-consp
                              consp-of-is-conjunct?
                              acl2::pseudo-termp-cadr-from-pseudo-term-listp
                              acl2::symbolp-of-car-when-symbol-listp
                              pseudo-term-listp-of-symbol-listp
                              acl2::pseudo-termp-opener))))
)

(skip-proofs
(defthm-replace-term-flag
  (defthm replace-if-maintains-term
    (implies (and (replace-options-p replace-options)
                  (type-options-p type-options)
                  (equal (typed-term->kind tterm) 'ifp)
                  (good-typed-term-p tterm))
             (equal (typed-term->term
                     (replace-if tterm replace-options type-options clock state))
                    (typed-term->term tterm)))
    :flag replace-if
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () ())
                              :expand (replace-if tterm replace-options
                                                  type-options clock state)))))
  (defthm replace-fncall-maintains-term
    (implies (and (replace-options-p replace-options)
                  (type-options-p type-options)
                  (equal (typed-term->kind tterm) 'fncallp)
                  (good-typed-term-p tterm))
             (equal (typed-term->term
                     (replace-fncall tterm replace-options type-options clock state))
                    (typed-term->term tterm)))
    :flag replace-fncall
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () ())
                   :expand (replace-fncall tterm replace-options type-options
                                           clock state)))))
  (defthm replace-term-maintains-term
    (implies (and (replace-options-p replace-options)
                  (type-options-p type-options)
                  (good-typed-term-p tterm))
             (equal (typed-term->term
                     (replace-term tterm replace-options type-options clock state))
                    (typed-term->term tterm)))
    :flag replace-term
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () ())
                   :expand (replace-term tterm replace-options type-options
                                         clock state)))))
  (defthm replace-term-list-maintains-term-lst
    (implies (and (replace-options-p replace-options)
                  (type-options-p type-options)
                  (good-typed-term-list-p tterm-lst))
             (equal (typed-term-list->term-lst
                     (replace-term-list tterm-lst replace-options type-options clock state))
                    (typed-term-list->term-lst tterm-lst)))
    :flag replace-term-list
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () ())
                   :expand
                   ((replace-term-list tterm-lst replace-options type-options
                                       clock state)
                    (replace-term-list nil replace-options type-options clock
                                       state)))))))
)

(skip-proofs
(defthm-replace-term-flag
  (defthm correctness-of-replace-if
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (replace-options-p replace-options)
                  (type-options-p type-options)
                  (equal (typed-term->kind tterm) 'ifp)
                  (good-typed-term-p tterm)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (replace-if tterm replace-options type-options clock state))
                       a))
    :flag replace-if
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d ()
                                   (pseudo-termp symbol-listp))
                              :expand (replace-if tterm replace-options
                                                  type-options clock state)))))
  (defthm correctness-of-replace-fncall
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (replace-options-p replace-options)
                  (type-options-p type-options)
                  (equal (typed-term->kind tterm) 'fncallp)
                  (good-typed-term-p tterm)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (replace-fncall tterm replace-options type-options
                                        clock state))
                       a))
    :flag replace-fncall
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d ()
                                   (pseudo-termp
                                    symbol-listp))
                              :expand (replace-fncall tterm replace-options
                                                      type-options clock state)))))
  (defthm correctness-of-replace-term
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (replace-options-p replace-options)
                  (type-options-p type-options)
                  (good-typed-term-p tterm)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (replace-term tterm replace-options type-options clock state))
                       a))
    :flag replace-term
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () (pseudo-termp))
                   :expand (replace-term tterm replace-options type-options
                                         clock state)))))
  (defthm correctness-of-replace-term-list
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (replace-options-p replace-options)
                  (type-options-p type-options)
                  (good-typed-term-list-p tterm-lst)
                  (alistp a)
                  (ev-smtcp (correct-typed-term-list tterm-lst) a))
             (ev-smtcp
              (correct-typed-term-list
               (replace-term-list tterm-lst replace-options type-options clock state))
              a))
    :flag replace-term-list
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d ()
                                   (pseudo-termp))
                   :expand
                   ((replace-term-list tterm-lst replace-options type-options
                                       clock state)
                    (replace-term-list nil replace-options type-options clock
                                       state))))))
  :hints(("Goal"
          :in-theory (disable pseudo-termp
                              symbol-listp))))
)

(define term-replacement-fn ((cl pseudo-term-listp)
                             (smtlink-hint t)
                             state)
  :returns (subgoal-lst pseudo-term-list-listp
                        :hints (("Goal" :in-theory (enable pseudo-termp))))
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint)) (list cl))
       (count (smtlink-hint->wrld-fn-len smtlink-hint))
       (goal (disjoin cl))
       (h (construct-replace-options smtlink-hint))
       ((type-options to) (construct-type-options smtlink-hint goal))
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
       (replaced-tterm (replace-term tterm h to count state))
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

(skip-proofs
(defthm correctness-of-type-replacement-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (term-replacement-cp cl hint state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :hints (("Goal"
           :do-not-induct t
           ;; :case-split-limitations (0 1)
           :in-theory (e/d (term-replacement-cp
                            term-replacement-fn
                            ;; correct-typed-term
                            )
                           ())
           ;; :use ((:instance correctness-of-replace-term
           ;;                  (tterm (typed-term (caddr (disjoin cl))
           ;;                                     ''t
           ;;                                     (cadr (disjoin cl))))
           ;;                  (replace-options (construct-replace-options hint))
           ;;                  (type-options (construct-type-options hint (disjoin cl)))
           ;;                  (a a)
           ;;                  (state state)))
           ))
  :rule-classes :clause-processor)
)
