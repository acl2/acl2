;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "typed-term-fns")
(include-book "returns-judgement")
(include-book "judgement-fns")
(include-book "../utils/fresh-vars")

(set-state-ok t)

(local (in-theory (disable (:executable-counterpart typed-term)
                           pseudo-termp pseudo-term-listp)))

;; choose-judge leaves only one type-predicate-of-term in the judgements
(encapsulate ()
  (local
   (in-theory (disable symbol-listp
                       pseudo-term-listp-of-symbol-listp
                       acl2::symbol-listp-when-not-consp
                       acl2::symbol-listp-of-cdr-when-symbol-listp
                       consp-of-pseudo-lambdap
                       acl2::pseudo-termp-opener
                       acl2-count)))

  (define choose-judge-helper ((judges pseudo-termp)
                               (term pseudo-termp)
                               (supertype type-to-types-alist-p)
                               (acc pseudo-termp)
                               (counter natp))
    :returns (mv (ctr natp)
                 (judge pseudo-termp))
    :measure (acl2-count (pseudo-term-fix judges))
    :verify-guards nil
    (b* ((judges (pseudo-term-fix judges))
         (term (pseudo-term-fix term))
         (acc (pseudo-term-fix acc))
         ((unless (is-judgements? judges term supertype))
          (prog2$ (er hard? 'type-inference-topdown=>choose-judge-helper
                      "Judges malformed: ~p0, term: ~p1~%" judges term)
                  (mv 0 ''t)))
         (counter (nfix counter))
         ((if (equal judges ''t)) (mv counter acc))
         ((if (and (type-predicate-of-term judges term supertype)
                   (zp counter)))
          (mv (1+ counter) `(if ,judges ,acc 'nil)))
         ((if (and (type-predicate-of-term judges term supertype)
                   (not (zp counter))))
          (mv counter acc))
         ((if (judgement-of-term judges term supertype))
          (mv counter `(if ,judges ,acc 'nil)))
         ((unless (is-conjunct? judges))
          (prog2$ (er hard? 'type-inference-topdown=>choose-judge-helper
                      "Judges should be a consp: ~q0" judges)
                  (mv counter acc)))
         ((list & cond then &) judges)
         ((mv new-ctr new-acc)
          (choose-judge-helper cond term supertype acc counter)))
      (choose-judge-helper then term supertype new-acc new-ctr)))
  )

(verify-guards choose-judge-helper)

(defthm correctness-of-choose-judge-helper
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judges)
                (pseudo-termp term)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp acc a)
                (ev-smtcp judges a))
           (ev-smtcp
            (mv-nth 1 (choose-judge-helper judges term supertype acc counter))
            a))
  :hints (("Goal"
           :in-theory (e/d (choose-judge-helper)
                           ()))))

(define choose-judge ((judges pseudo-termp)
                      (term pseudo-termp)
                      (supertype type-to-types-alist-p))
  :returns (judge (pseudo-termp judge))
  (b* (((mv & judge)
        (choose-judge-helper judges term supertype ''t 0)))
    judge))

(defthm correctness-of-choose-judge
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judges)
                (pseudo-termp term)
                (alistp a)
                (ev-smtcp judges a))
           (ev-smtcp (choose-judge judges term supertype) a))
  :hints (("Goal"
           :in-theory (e/d (choose-judge)
                           ()))))

;;----------------------------------------------------------------
(define unify-expected ((judge pseudo-termp)
                        (term pseudo-termp)
                        (expected pseudo-termp)
                        (supertype type-to-types-alist-p))
  :returns (new-judge pseudo-termp)
  (b* ((judge (pseudo-term-fix judge))
       (term (pseudo-term-fix term))
       (expected (pseudo-term-fix expected))
       (supertype (type-to-types-alist-fix supertype))
       ((if (equal expected ''t))
        (choose-judge judge term supertype))
       ((if (path-test judge expected)) expected))
    (choose-judge judge term supertype)))

(defthm correctness-of-unify-expected
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (typed-term-p tterm)
                (pseudo-termp expected)
                (alistp a)
                (ev-smtcp (correct-typed-term tterm) a))
           (ev-smtcp
            (correct-typed-term
             (typed-term
              (typed-term->term tterm)
              (typed-term->path-cond tterm)
              (unify-expected (typed-term->judgements tterm)
                              (typed-term->term tterm)
                              expected supertype)))
            a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (unify-expected
                            correct-typed-term)
                           (correctness-of-path-test-list-corollary
                            symbol-listp
                            consp-of-pseudo-lambdap
                            correctness-of-path-test))
           :use ((:instance correctness-of-path-test
                            (path-cond (typed-term->judgements tterm))
                            (expr expected)
                            (a a))))))

(define unify-variable ((tterm t)
                        (expected pseudo-termp)
                        (options type-options-p))
  :guard (and (good-typed-term-p tterm)
              (equal (typed-term->kind tterm) 'variablep))
  :returns (new-tt (good-typed-term-p new-tt)
                   :hints (("Goal"
                            :in-theory (enable good-typed-variable-p))))
  (b* (((unless (mbt (and (pseudo-termp expected)
                          (equal (typed-term->kind tterm) 'variablep)
                          (good-typed-term-p tterm))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((type-options to) options)
       ((unless (is-judgements? expected tt.term to.supertype))
        (prog2$
         (er hard? 'type-inference-topdown=>unify-variable
             "Expected ~p0 is not a conjunct list for ~p1.~%" expected tt.term)
         tterm)))
    (make-typed-term :term tt.term
                     :path-cond tt.path-cond
                     :judgements (unify-expected tt.judgements tt.term expected
                                                 to.supertype)))
  ///
  (more-returns
   (new-tt (implies (and (pseudo-termp expected)
                         (type-options-p options)
                         (equal (typed-term->kind tterm) 'variablep)
                         (good-typed-term-p tterm))
                    (equal (typed-term->path-cond new-tt)
                           (typed-term->path-cond tterm)))
           :name unify-variable-maintains-path-cond))
  (defthm correctness-of-unify-variable
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (type-options-p options)
                  (equal (typed-term->kind tterm) 'variablep)
                  (good-typed-term-p tterm)
                  (pseudo-termp expected)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (unify-variable tterm expected options))
                       a)))
  (defthm unify-variable-maintains-term
    (implies (and (type-options-p options)
                  (pseudo-termp expected)
                  (equal (typed-term->kind tterm) 'variablep)
                  (good-typed-term-p tterm))
             (equal (typed-term->term
                     (unify-variable tterm expected options))
                    (typed-term->term tterm)))))

(define unify-quote ((tterm typed-term-p)
                     (expected pseudo-termp)
                     (options type-options-p))
  :guard (and (good-typed-term-p tterm)
              (equal (typed-term->kind tterm) 'quotep))
  :returns (new-tt (good-typed-term-p new-tt)
                   :hints (("Goal"
                            :in-theory (enable good-typed-quote-p))))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (pseudo-termp expected)
                          (equal (typed-term->kind tterm) 'quotep)
                          (good-typed-term-p tterm))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((type-options to) options)
       ((unless (is-judgements? expected tt.term to.supertype))
        (prog2$
         (er hard? 'type-inference-topdown=>unify-variable
             "Expected ~p0 is not a conjunct list.~%" expected)
         tterm)))
    (make-typed-term :term tt.term
                     :path-cond tt.path-cond
                     :judgements (unify-expected tt.judgements tt.term expected
                                                 to.supertype)))
  ///
  (more-returns
   (new-tt (implies (and (pseudo-termp expected)
                         (equal (typed-term->kind tterm) 'quotep)
                         (good-typed-term-p tterm))
                    (equal (typed-term->path-cond new-tt)
                           (typed-term->path-cond tterm)))
           :name unify-quote-maintains-path-cond))
  (defthm correctness-of-unify-quote
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (type-options-p options)
                  (typed-term-p tterm)
                  (pseudo-termp expected)
                  (equal (typed-term->kind tterm) 'quotep)
                  (good-typed-term-p tterm)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (unify-quote tterm expected options))
                       a)))
  (defthm unify-quote-maintains-term
    (implies (and (type-options-p options)
                  (pseudo-termp expected)
                  (equal (typed-term->kind tterm) 'quotep)
                  (good-typed-term-p tterm))
             (equal (typed-term->term
                     (unify-quote tterm expected options))
                    (typed-term->term tterm)))))

(define unify-if-top ((judge pseudo-termp)
                      (term pseudo-termp)
                      (filter-judge pseudo-termp)
                      (filter-term pseudo-termp)
                      (options type-options-p))
  :returns (new-judge pseudo-termp)
  (b* ((judge (pseudo-term-fix judge))
       (term (pseudo-term-fix term))
       (filter-judge (pseudo-term-fix filter-judge))
       (filter-term (pseudo-term-fix filter-term))
       (options (type-options-fix options))
       (supertype-alst (type-options->supertype options))
       (new-var (new-fresh-var (type-options->names options)))
       ((mv filter-fast &)
        (make-fast-judgements filter-judge filter-term
                              new-var supertype-alst nil 0))
       (ind-lst
        (map-judgements judge term new-var supertype-alst filter-fast))
       ((mv judge-common &)
        (construct-judge-by-list judge term supertype-alst ind-lst ''t)))
    judge-common))

(defthm correctness-of-unify-if-top
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judge)
                (pseudo-termp term)
                (pseudo-termp filter-judge)
                (pseudo-termp filter-term)
                (alistp a)
                (ev-smtcp judge a)
                (ev-smtcp filter-judge a))
           (ev-smtcp (unify-if-top judge term filter-judge filter-term
                                   options)
                     a))
  :hints (("Goal"
           :in-theory (e/d (unify-if-top)
                           ()))))

(defines unify-type
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil
  :hints (("Goal"
           :in-theory (e/d ()
                           (acl2-count implies-of-fncall-kind))))

  (define unify-fncall ((tterm typed-term-p)
                        (expected pseudo-termp)
                        (options type-options-p)
                        state)
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'fncallp))
    :returns (new-tt (good-typed-term-p new-tt))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (pseudo-termp expected)
                            (equal (typed-term->kind tterm) 'fncallp)
                            (good-typed-term-p tterm))))
          (make-typed-term))
         ((type-options to) options)
         ((typed-term tt) tterm)
         ((cons fn actuals) tt.term)
         (tt-actuals (typed-term-fncall->actuals tt))
         (tta.path-cond (typed-term-list->path-cond tt-actuals))
         (tta.judgements (typed-term-list->judgements tt-actuals))
         ((typed-term ttt) (typed-term->top tt))
         (judge-top
          (unify-expected ttt.judgements ttt.term expected to.supertype))
         (new-top (make-typed-term :term ttt.term
                                   :path-cond ttt.path-cond
                                   :judgements judge-top))
         (conspair (assoc-equal fn to.functions))
         ((unless conspair)
          (prog2$ (er hard? 'type-inference-topdown=>unify-fncall
                      "There exists no function description for function ~p0. ~
                       ~%" fn)
                  tt))
         (fn-description (cdr conspair))
         (expected-actuals
          (choose-returns judge-top fn actuals tta.judgements tta.path-cond
                          fn-description to state))
         (new-actuals (unify-type-list tt-actuals expected-actuals to state))
         ;; in order to satisfy the guards of make-typed-fncall
         ((unless (make-typed-fncall-guard new-top new-actuals))
          tt))
      (make-typed-fncall new-top new-actuals)))

  (define unify-if ((tterm typed-term-p)
                    (expected pseudo-termp)
                    (options type-options-p)
                    state)
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'ifp))
    :returns (new-tt (good-typed-term-p new-tt))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp expected)
                            (type-options-p options)
                            (equal (typed-term->kind tterm) 'ifp)
                            (good-typed-term-p tterm))))
          (make-typed-term))
         ((type-options to) options)
         ((typed-term tt) tterm)
         ((typed-term tt-cond) (typed-term-if->cond tt))
         ((typed-term tt-then) (typed-term-if->then tt))
         ((typed-term tt-else) (typed-term-if->else tt))
         ((typed-term tt-top) (typed-term->top tt))
         (new-cond (unify-type tt-cond ''t to state))
         (judge-top
          (unify-expected tt-top.judgements tt-top.term expected to.supertype))
         (new-top (make-typed-term :term tt-top.term
                                   :path-cond tt-top.path-cond
                                   :judgements judge-top))
         (judge-then-top
          (type-judgement-top tt-then.judgements tt-then.term options))
         (judge-else-top
          (type-judgement-top tt-else.judgements tt-else.term options))
         (then-expected (unify-if-top judge-then-top tt-then.term
                                      judge-top tt-top.term
                                      options))
         (else-expected (unify-if-top judge-else-top tt-else.term
                                      judge-top tt-top.term
                                      options))
         (new-then (unify-type tt-then then-expected to state))
         (new-else (unify-type tt-else else-expected to state)))
      (make-typed-if new-top new-cond new-then new-else)))

  (define unify-type ((tterm typed-term-p)
                      (expected pseudo-termp)
                      (options type-options-p)
                      state)
    :guard (good-typed-term-p tterm)
    :returns (new-tt (good-typed-term-p new-tt))
    :measure (list (acl2-count (typed-term->term tterm)) 1)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (pseudo-termp expected)
                            (good-typed-term-p tterm))))
          (make-typed-term))
         ((if (equal (typed-term->kind tterm) 'variablep))
          (unify-variable tterm expected options))
         ((if (equal (typed-term->kind tterm) 'quotep))
          (unify-quote tterm expected options))
         ((if (equal (typed-term->kind tterm) 'ifp))
          (unify-if tterm expected options state))
         ((unless (typed-term->kind tterm))
          ;;(unify-lambda tterm expected options state)
          (prog2$ (er hard? 'type-inference-topdown=>unify-type
                      "Found lambda term in goal.~%")
                  tterm)))
      (unify-fncall tterm expected options state)))

  (define unify-type-list ((tterm-lst typed-term-list-p)
                           (expected-lst pseudo-term-listp)
                           (options type-options-p)
                           state)
    :returns (new-ttl (good-typed-term-list-p new-ttl))
    :guard (good-typed-term-list-p tterm-lst)
    :measure (list (acl2-count (typed-term-list->term-lst tterm-lst))
                   1)
    (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                            (type-options-p options)
                            (pseudo-term-listp expected-lst)
                            (good-typed-term-list-p tterm-lst))))
          nil)
         ((unless (consp tterm-lst)) nil)
         ((cons tterm-hd tterm-tl) tterm-lst)
         ((unless (consp expected-lst))
          (prog2$
           (er hard? 'type-inference-topdown=>unify-type-list
               "Expected-lst is already empty while there are still ~
             typed-terms.~%")
           tterm-lst))
         ((cons expected-hd expected-tl) expected-lst)
         (tt-car (unify-type tterm-hd expected-hd options state))
         (tt-cdr (unify-type-list tterm-tl expected-tl options state))
         ((unless (implies (consp tt-cdr)
                           (equal (typed-term->path-cond tt-car)
                                  (typed-term-list->path-cond tt-cdr))))
          tterm-lst))
      (cons tt-car tt-cdr)))
  ///
  (defthm typed-term-of-unify-fncall
    (typed-term-p (unify-fncall tterm expected options state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (unify-fncall tterm expected options state)))))))
  (defthm typed-term-of-unify-if
    (typed-term-p (unify-if tterm expected options state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (unify-if tterm expected options state)))))))
  (defthm typed-term-of-unify-type
    (typed-term-p (unify-type tterm expected options state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (unify-type tterm expected options state)))))))
  (defthm typed-term-list-of-unify-type-list
    (typed-term-list-p
     (unify-type-list tterm-lst expected-lst options state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-list-implies-typed-term-list)
             :use ((:instance good-typed-term-list-implies-typed-term-list
                              (tterm-lst
                               (unify-type-list tterm-lst expected-lst
                                                options state)))))))
  )

(verify-guards unify-type
  :hints (("Goal"
           :in-theory (enable make-typed-fncall-guard
                              typed-term-list->path-cond
                              typed-term-fncall->actuals))))

(defthm-unify-type-flag
  (defthm correctness-of-unify-if
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp expected)
                  (type-options-p options)
                  (equal (typed-term->kind tterm) 'ifp)
                  (good-typed-term-p tterm)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (unify-if tterm expected options state))
                       a))
    :flag unify-if
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d ()
                                   (pseudo-termp
                                    symbol-listp
                                    EV-SMTCP-OF-LAMBDA
                                    CORRECTNESS-OF-PATH-TEST-LIST-COROLLARY
                                    CONSP-OF-PSEUDO-LAMBDAP
                                    ACL2::PSEUDO-TERMP-OPENER
                                    LAMBDA-OF-PSEUDO-LAMBDAP
                                    EV-SMTCP-OF-BOOLEANP-CALL
                                    PSEUDO-LAMBDAP-OF-FN-CALL-OF-PSEUDO-TERMP
                                    PSEUDO-TERM-LISTP-OF-CDR-OF-PSEUDO-TERMP
                                    typed-term->top-maintains-path-cond
                                    typed-term->top-maintains-term
                                    typed-term-if->cond-maintains-term
                                    typed-term-if->then-maintains-term
                                    typed-term-if->else-maintains-term
                                    make-typed-fncall-maintains-term))
                              :expand (unify-if tterm expected options state)))))
  (defthm correctness-of-unify-fncall
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (type-options-p options)
                  (pseudo-termp expected)
                  (equal (typed-term->kind tterm) 'fncallp)
                  (good-typed-term-p tterm)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (unify-fncall tterm expected options state))
                       a))
    :flag unify-fncall
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d ()
                                   (pseudo-termp
                                    symbol-listp
                                    EV-SMTCP-OF-LAMBDA
                                    CORRECTNESS-OF-PATH-TEST-LIST-COROLLARY
                                    CONSP-OF-PSEUDO-LAMBDAP
                                    ACL2::PSEUDO-TERMP-OPENER
                                    LAMBDA-OF-PSEUDO-LAMBDAP
                                    EV-SMTCP-OF-BOOLEANP-CALL
                                    PSEUDO-LAMBDAP-OF-FN-CALL-OF-PSEUDO-TERMP
                                    PSEUDO-TERM-LISTP-OF-CDR-OF-PSEUDO-TERMP
                                    typed-term->top-maintains-path-cond
                                    typed-term->top-maintains-term
                                    typed-term-if->cond-maintains-term
                                    typed-term-if->then-maintains-term
                                    typed-term-if->else-maintains-term
                                    make-typed-fncall-maintains-term))
                   :expand (unify-fncall tterm expected options state)))))
  (defthm correctness-of-unify-type
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (type-options-p options)
                  (pseudo-termp expected)
                  (good-typed-term-p tterm)
                  (alistp a)
                  (ev-smtcp (correct-typed-term tterm) a))
             (ev-smtcp (correct-typed-term
                        (unify-type tterm expected options state))
                       a))
    :flag unify-type
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () (pseudo-termp))
                   :expand (unify-type tterm expected options state)))))
  (defthm correctness-of-unify-type-list
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (type-options-p options)
                  (pseudo-term-listp expected-lst)
                  (good-typed-term-list-p tterm-lst)
                  (alistp a)
                  (ev-smtcp (correct-typed-term-list tterm-lst) a))
             (ev-smtcp
              (correct-typed-term-list
               (unify-type-list tterm-lst expected-lst options state))
              a))
    :flag unify-type-list
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d ()
                                   (pseudo-termp))
                   :expand
                   ((unify-type-list tterm-lst expected-lst options state)
                    (unify-type-list nil expected-lst options state)
                    (unify-type-list tterm-lst nil options state)
                    (unify-type-list nil nil options state))))))
  :hints(("Goal"
          :in-theory (disable pseudo-termp
                              symbol-listp
                              EV-SMTCP-OF-LAMBDA
                              CORRECTNESS-OF-PATH-TEST-LIST-COROLLARY
                              CONSP-OF-PSEUDO-LAMBDAP
                              ACL2::PSEUDO-TERMP-OPENER
                              LAMBDA-OF-PSEUDO-LAMBDAP
                              EV-SMTCP-OF-BOOLEANP-CALL
                              PSEUDO-LAMBDAP-OF-FN-CALL-OF-PSEUDO-TERMP
                              PSEUDO-TERM-LISTP-OF-CDR-OF-PSEUDO-TERMP
                              typed-term->top-maintains-path-cond
                              typed-term->top-maintains-term
                              typed-term-if->cond-maintains-term
                              typed-term-if->then-maintains-term
                              typed-term-if->else-maintains-term
                              make-typed-fncall-maintains-term))))

(defthm-unify-type-flag
  (defthm unify-if-maintains-path-cond
    (implies (and (pseudo-termp expected)
                  (type-options-p options)
                  (equal (typed-term->kind tterm) 'ifp)
                  (good-typed-term-p tterm))
             (equal (typed-term->path-cond
                     (unify-if tterm expected options state))
                    (typed-term->path-cond tterm)))
    :flag unify-if
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
                              :expand (unify-if tterm expected options state)))))
  (defthm unify-fncall-maintains-path-cond
    (implies (and (type-options-p options)
                  (pseudo-termp expected)
                  (equal (typed-term->kind tterm) 'fncallp)
                  (good-typed-term-p tterm))
             (equal (typed-term->path-cond
                     (unify-fncall tterm expected options state))
                    (typed-term->path-cond tterm)))
    :flag unify-fncall
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
                   :expand (unify-fncall tterm expected options state)))))
  (defthm unify-type-maintains-path-cond
    (implies (and (type-options-p options)
                  (pseudo-termp expected)
                  (good-typed-term-p tterm))
             (equal (typed-term->path-cond
                     (unify-type tterm expected options state))
                    (typed-term->path-cond tterm)))
    :flag unify-type
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () ())
                   :expand (unify-type tterm expected options state)))))
  (defthm unify-type-list-maintains-path-cond
    (implies (and (type-options-p options)
                  (pseudo-term-listp expected-lst)
                  (good-typed-term-list-p tterm-lst))
             (equal (typed-term-list->path-cond
                     (unify-type-list tterm-lst expected-lst options state))
                    (typed-term-list->path-cond tterm-lst)))
    :flag unify-type-list
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
                   ((unify-type-list tterm-lst expected-lst options state)
                    (unify-type-list nil expected-lst options state)
                    (unify-type-list tterm-lst nil options state)
                    (unify-type-list nil nil options state))))))
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

(defthm-unify-type-flag
  (defthm unify-if-maintains-term
    (implies (and (pseudo-termp expected)
                  (type-options-p options)
                  (equal (typed-term->kind tterm) 'ifp)
                  (good-typed-term-p tterm))
             (equal (typed-term->term
                     (unify-if tterm expected options state))
                    (typed-term->term tterm)))
    :flag unify-if
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (make-typed-if) ())
                              :expand (unify-if tterm expected options state)))))
  (defthm unify-fncall-maintains-term
    (implies (and (type-options-p options)
                  (pseudo-termp expected)
                  (equal (typed-term->kind tterm) 'fncallp)
                  (good-typed-term-p tterm))
             (equal (typed-term->term
                     (unify-fncall tterm expected options state))
                    (typed-term->term tterm)))
    :flag unify-fncall
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () ())
                   :expand (unify-fncall tterm expected options state)))))
  (defthm unify-type-maintains-term
    (implies (and (type-options-p options)
                  (pseudo-termp expected)
                  (good-typed-term-p tterm))
             (equal (typed-term->term
                     (unify-type tterm expected options state))
                    (typed-term->term tterm)))
    :flag unify-type
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d () ())
                   :expand (unify-type tterm expected options state)))))
  (defthm unify-type-list-maintains-term-lst
    (implies (and (type-options-p options)
                  (pseudo-term-listp expected-lst)
                  (good-typed-term-list-p tterm-lst))
             (equal (typed-term-list->term-lst
                     (unify-type-list tterm-lst expected-lst options state))
                    (typed-term-list->term-lst tterm-lst)))
    :flag unify-type-list
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (typed-term-list->term-lst) ())
                   :expand
                   ((unify-type-list tterm-lst expected-lst options state)
                    (unify-type-list nil expected-lst options state)
                    (unify-type-list tterm-lst nil options state)
                    (unify-type-list nil nil options state)))))))

(define type-judge-topdown-cp ((cl pseudo-term-listp)
                               (smtlink-hint t)
                               state)
  (b* (((unless (pseudo-term-listp cl)) (value nil))
       ((unless (smtlink-hint-p smtlink-hint)) (value (list cl)))
       (- (cw "cl: ~q0" cl))
       (goal (disjoin cl))
       (h (construct-type-options smtlink-hint goal))
       ((mv okp tterm)
        (case-match goal
          (('implies judges term)
           (mv t (make-typed-term :term term
                                  :path-cond ''t
                                  :judgements judges)))
          (& (mv nil (make-typed-term)))))
       ((unless okp)
        (prog2$ (er hard? 'type-inference-topdown=>type-judge-topdown-cp
                    "The input term is of wrong shape. It should look like ~
                     (typed-goal ...) ~%")
                (value (list cl))))
       ((unless (good-typed-term-p tterm))
        (prog2$ (er hard? 'type-inference-topdown=>type-judge-topdown-cp
                    "Not a good-typed-term-p: ~q0" tterm)
                (value (list cl))))
       (unified-tterm (unify-type tterm ''t h state))
       (unified-judgements (typed-term->judgements unified-tterm))
       (unified-term (typed-term->term unified-tterm))
       (new-cl `((implies ,unified-judgements ,unified-term)))
       (next-cp (cdr (assoc-equal 'type-judge-topdown *SMT-architecture*)))
       ((if (null next-cp)) (value (list cl)))
       (the-hint
        `(:clause-processor (,next-cp clause ',smtlink-hint state)))
       (hinted-goal `((hint-please ',the-hint) ,@new-cl))
       (- (cw "type-judge-topdown-cp: ~q0" hinted-goal)))
    (value (list hinted-goal))))

(defthm correctness-of-type-judge-topdown-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (type-judge-topdown-cp cl hints state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (type-judge-topdown-cp correct-typed-term disjoin)
                           (correctness-of-unify-type
                            unify-type-maintains-path-cond
                            unify-type-maintains-term))
           :use ((:instance correctness-of-unify-type
                            (options (construct-type-options hints (disjoin cl)))
                            (expected ''t)
                            (tterm (typed-term (caddr (disjoin cl))
                                               ''t
                                               (cadr (disjoin cl))))
                            (a a)
                            (state state))
                 (:instance unify-type-maintains-path-cond
                            (options (construct-type-options hints (disjoin cl)))
                            (expected ''t)
                            (tterm (typed-term (caddr (disjoin cl))
                                               ''t
                                               (cadr (disjoin cl)))))
                 (:instance unify-type-maintains-term
                            (options (construct-type-options hints (disjoin cl)))
                            (expected ''t)
                            (tterm (typed-term (caddr (disjoin cl))
                                               ''t
                                               (cadr (disjoin cl))))))))
  :rule-classes :clause-processor)
