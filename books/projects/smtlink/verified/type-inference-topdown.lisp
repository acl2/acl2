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

(set-state-ok t)

(define look-up-judge-list ((term-lst pseudo-term-listp)
                            (judge pseudo-termp)
                            (supertype type-to-types-alist-p))
  :returns (jugde-lst pseudo-term-listp)
  (b* ((term-lst (pseudo-term-list-fix term-lst))
       (judge (pseudo-term-fix judge))
       (supertype (type-to-types-alist-fix supertype))
       ((unless (consp term-lst)) nil)
       ((cons term-hd term-tl) term-lst)
       (judge-hd (look-up-path-cond term-hd judge supertype))
       ((unless (is-conjunct? judge-hd))
        (er hard? 'type-inference-topdpwn=>look-up-judge-list
            "~p0 is not a conjunct.~%" judge-hd)))
    (cons judge-hd (look-up-judge-list term-tl judge supertype))))

(local (in-theory (disable (:executable-counterpart typed-term))))

(encapsulate ()
  (local
   (in-theory (disable symbol-listp
                       pseudo-term-listp-of-symbol-listp
                       acl2::symbol-listp-when-not-consp
                       acl2::pseudo-termp-opener
                       acl2-count)))

  (define choose-judge-helper ((judges pseudo-termp)
                               (term pseudo-termp)
                               (supertype type-to-types-alist-p)
                               (acc pseudo-termp)
                               (counter natp))
    :guard (is-conjunct-list? acc term supertype)
    :returns (mv (ctr natp)
                 (judge (and (pseudo-termp judge)
                             (is-conjunct-list? judge term supertype))
                        :hyp :guard))
    :measure (acl2-count (pseudo-term-fix judges))
    :verify-guards nil
    (b* ((judges (pseudo-term-fix judges))
         (term (pseudo-term-fix term))
         (acc (pseudo-term-fix acc))
         ((unless (mbt (is-conjunct-list? acc term supertype)))
          (mv 0 ''t))
         (counter (nfix counter))
         ((if (equal judges ''t)) (mv counter acc))
         ((if (and (type-predicate-of-term judges term supertype)
                   (zp counter)))
          (mv (1+ counter)
              `(if ,judges ,acc 'nil)))
         ((if (and (type-predicate-of-term judges term supertype)
                   (not (zp counter))))
          (mv counter acc))
         ((unless (is-conjunct? judges))
          (prog2$ (er hard? 'type-inference-topdown=>choose-judge
                      "Judges should be a conjunct: ~q0" judges)
                  (mv counter acc)))
         ((list & cond then &) judges)
         ((mv new-ctr new-acc)
          (choose-judge-helper cond term supertype acc counter)))
      (choose-judge-helper then term supertype new-acc new-ctr)))

  (verify-guards choose-judge-helper)
  )

(define choose-judge ((judges pseudo-termp)
                      (term pseudo-termp)
                      (supertype type-to-types-alist-p))
  :returns (judge (and (pseudo-termp judge)
                       (is-conjunct-list? judge term supertype))
                  :hyp :guard)
  (b* (((mv & judge)
        (choose-judge-helper judges term supertype ''t 0)))
    judge))

;;-----------------------------------------------------

(define initialize-actuals-judges-alist ((actuals pseudo-term-listp))
  :returns (actuals-alst pseudo-term-alistp)
  (b* ((actuals (pseudo-term-list-fix actuals))
       ((unless (consp actuals)) nil)
       ((cons first rest) actuals))
    (acons first ''t (initialize-actuals-judges-alist rest))))

(define count-type-predicates ((judge pseudo-termp)
                               (term pseudo-termp)
                               (supertype type-to-types-alist-p)
                               (counter natp))
  :returns (new-counter natp)
  :measure (acl2-count (pseudo-term-fix judge))
  (b* ((judge (pseudo-term-fix judge))
       (counter (nfix counter))
       ((if (equal judge ''t)) counter)
       ((if (type-predicate-of-term judge term supertype))
        (1+ counter))
       ((unless (is-conjunct? judge)) counter)
       ((list & hd tl &) judge)
       (new-counter (count-type-predicates hd term supertype counter)))
    (count-type-predicates tl term supertype new-counter)))

(define atmost-one-type-predicate ((judge pseudo-termp)
                                   (term pseudo-termp)
                                   (supertype type-to-types-alist-p))
  :returns (ok booleanp)
  (if (<= (count-type-predicates judge term supertype 0) 1) t nil))

(encapsulate ()
  (local (in-theory (disable symbol-listp acl2::pseudo-termp-opener
                             member-equal)))

  (define generate-actuals-judges-one ((hypo pseudo-termp)
                                       (formal symbolp)
                                       (actual pseudo-termp)
                                       (actuals-judges-alst pseudo-term-alistp)
                                       (supertype type-to-types-alist-p)
                                       state)
    :returns (new-alst pseudo-term-alistp)
    (b* ((hypo (pseudo-term-fix hypo))
         (actual (pseudo-term-fix actual))
         (formal-judges (look-up-path-cond formal hypo supertype))
         (actual-judges (term-substitution formal-judges `((,formal . ,actual)) t))
         (actuals-judges-alst (pseudo-term-alist-fix actuals-judges-alst))
         (yes? (assoc-equal actual actuals-judges-alst))
         ((unless yes?)
          (er hard? 'type-inference-topdown=>generate-actuals-judges-one
              "Actual ~p0 doesn't exist in alist ~p1~%" actual
              actuals-judges-alst))
         (judge-acc (cdr yes?))
         (new-judge (union-judgements actual-judges judge-acc state))
         (yes? (atmost-one-type-predicate new-judge actual supertype))
         ((unless yes?) nil))
      (acons actual new-judge actuals-judges-alst)))
  )

(encapsulate ()
  (local (in-theory (disable pseudo-termp symbol-listp)))

  (define generate-actuals-judges ((hypo pseudo-termp)
                                   (formals symbol-listp)
                                   (actuals pseudo-term-listp)
                                   (actuals-judges-alst pseudo-term-alistp)
                                   (supertype type-to-types-alist-p)
                                   state)
    :returns (new-alst pseudo-term-alistp)
    :measure (len (symbol-list-fix formals))
    (b* ((formals (symbol-list-fix formals))
         (actuals (pseudo-term-list-fix actuals))
         (actuals-judges-alst (pseudo-term-alist-fix actuals-judges-alst))
         ((unless (consp formals)) actuals-judges-alst)
         ((unless (consp actuals)) actuals-judges-alst)
         ((cons formals-hd formals-tl) formals)
         ((cons actuals-hd actuals-tl) actuals)
         (new-acc
          (generate-actuals-judges-one hypo formals-hd actuals-hd
                                       actuals-judges-alst supertype
                                       state))
         ((unless new-acc) nil))
      (generate-actuals-judges hypo formals-tl actuals-tl new-acc supertype
                               state)))
  )

(encapsulate ()
  (local (in-theory (disable symbol-listp
                             consp-of-is-conjunct?
                             consp-of-pseudo-lambdap
                             acl2::pseudo-termp-opener
                             pseudo-termp
                             true-listp
                             true-list-listp
                             equal-fixed-and-x-of-pseudo-termp
                             acl2::symbol-listp-when-not-consp
                             member-equal
                             equal-pseudo-term-list-fix
                             pseudo-term-listp
                             pseudo-term-alistp-when-not-consp)))

  ;; For each returns theorems, get conclusion, extend the conclusion.
  ;; check if the judge-top includes the conclusion. If so, construct
  ;; actuals-judges based on its hypotheses. Pay attention not to add duplicated
  ;; judgements and there should only be one type predicate. If there are
  ;; multiple type predicates, continue. Do this util all judge-top is covered.
  ;; If by the end, not all judge-top is covered, complain.
  (define choose-returns-helper ((return-judge pseudo-termp)
                                 (returns-thms returns-list-p)
                                 (fn symbolp)
                                 (actuals pseudo-term-listp)
                                 (path-cond pseudo-termp)
                                 (conclusion-acc pseudo-termp)
                                 (actuals-judges-acc pseudo-term-alistp)
                                 (options type-options-p)
                                 (single? booleanp)
                                 state)
    :guard (not (equal fn 'quote))
    :returns (mv (conclusion pseudo-termp)
                 (actuals-judges pseudo-term-alistp))
    :measure (len (returns-list-fix returns-thms))
    :verify-guards nil
    (b* ((return-judge (pseudo-term-fix return-judge))
         (returns-thms (returns-list-fix returns-thms))
         (fn (symbol-fix fn))
         (actuals (pseudo-term-list-fix actuals))
         (conclusion-acc (pseudo-term-fix conclusion-acc))
         (actuals-judges-acc (pseudo-term-alist-fix actuals-judges-acc))
         (options (type-options-fix options))
         ((type-options to) options)
         ((if (path-test-list conclusion-acc return-judge state))
          (mv conclusion-acc actuals-judges-acc))
         ((unless (consp returns-thms)) (mv nil nil))
         ((cons returns-hd returns-tl) returns-thms)
         ((returns re) returns-hd)
         ((mv hypo concl)
          (case-match re.returns-thm
            ((('lambda (r) conclusions) (!fn . !re.formals))
             (mv ''t (term-substitution conclusions `((,r . (,fn ,@re.formals))) t)))
            (('implies type-predicates conclusions)
             (mv type-predicates conclusions))
            (& (mv ''t re.returns-thm))))
         (substed-concl
          (term-substitution concl `(((,fn ,@re.formals) . (,fn ,@actuals))) t))
         (extended-concl (extend-judgements substed-concl path-cond options state))
         ;; return-judge implies extended-concl
         ((unless (path-test-list-or return-judge extended-concl state))
          (choose-returns-helper return-judge returns-tl fn actuals path-cond
                                 conclusion-acc actuals-judges-acc options
                                 single? state))
         ((if (and single? (path-test-list extended-concl return-judge state)))
          (b* ((new-actuals-judges
                (generate-actuals-judges hypo re.formals actuals
                                         (initialize-actuals-judges-alist
                                          actuals)
                                         to.supertype state))
               ((if new-actuals-judges) (mv substed-concl new-actuals-judges)))
            (choose-returns-helper return-judge returns-tl fn actuals path-cond
                                   conclusion-acc actuals-judges-acc options
                                   single? state)))
         ((if single?)
          (choose-returns-helper return-judge returns-tl fn actuals path-cond
                                 conclusion-acc actuals-judges-acc options
                                 single? state))
         (new-concl (union-judgements conclusion-acc extended-concl state))
         (new-actuals-judges
          (generate-actuals-judges hypo re.formals actuals actuals-judges-acc
                                   to.supertype state))
         ((unless new-actuals-judges)
          (choose-returns-helper return-judge returns-tl fn actuals path-cond
                                 conclusion-acc actuals-judges-acc options
                                 single? state)))
      (choose-returns-helper return-judge returns-tl fn actuals path-cond new-concl
                             new-actuals-judges options single? state)))
  )

(verify-guards choose-returns-helper
  :hints (("Goal"
           :in-theory (disable symbol-listp consp-of-is-conjunct?
                               consp-of-pseudo-lambdap
                               acl2::pseudo-termp-opener
                               acl2::symbol-listp-when-not-consp
                               member-equal
                               true-list-listp
                               acl2::true-listp-of-car-when-true-list-listp))))

(define choose-returns ((return-judge pseudo-termp)
                        (returns-thms returns-list-p)
                        (fn symbolp)
                        (actuals pseudo-term-listp)
                        (path-cond pseudo-termp)
                        (options type-options-p)
                        (single? booleanp)
                        state)
  :returns (actuals-judges pseudo-term-alistp)
  :guard (not (equal fn 'quote))
  (b* (((mv & actuals-judges)
        (choose-returns-helper return-judge returns-thms fn actuals
                               path-cond ''t
                               (initialize-actuals-judges-alist actuals)
                               options single? state)))
    actuals-judges))

(local
 (defthm assoc-equal-of-pseudo-term-alistp
   (implies
    (and (pseudo-termp x)
         (pseudo-term-alistp y)
         (assoc-equal x y))
    (pseudo-termp (cdr (assoc-equal x y))))
   ))

(define get-actuals-judges ((actuals pseudo-term-listp)
                            (actuals-judges-alst pseudo-term-alistp))
  :returns (actuals-judges pseudo-term-listp)
  (b* ((actuals (pseudo-term-list-fix actuals))
       (actuals-judges-alst (pseudo-term-alist-fix actuals-judges-alst))
       ((unless (consp actuals)) nil)
       ((cons ahd atl) actuals)
       (yes? (assoc-equal ahd actuals-judges-alst))
       ((unless yes?)
        (er hard? 'type-inference-topdown=>get-actuals-judges
            "Actual ~p0 doesn't exist in alist ~p1~%" ahd
            actuals-judges-alst))
       (judge-hd (cdr yes?)))
    (cons judge-hd (get-actuals-judges atl actuals-judges-alst))))

;;----------------------------------------------------------------

(define unify-variable ((tterm t)
                        (expected pseudo-termp)
                        (options type-options-p))
  :guard (and (good-typed-term-p tterm options)
              (equal (typed-term->kind tterm) 'variablep))
  :guard-debug t
  :returns (new-tt (good-typed-term-p new-tt options)
                   :hints (("Goal"
                            :in-theory (enable good-typed-variable-p))))
  (b* (((unless (mbt (and (pseudo-termp expected)
                          (equal (typed-term->kind tterm) 'variablep)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((type-options to) options)
       ((unless (is-conjunct-list? expected tt.term to.supertype))
        (prog2$
         (er hard? 'type-inference-topdown=>unify-variable
             "Expected ~p0 is not a conjunct list.~%" expected)
         tterm))
       ((unless (equal expected ''t))
        (make-typed-term :term tt.term
                         :path-cond tt.path-cond
                         :judgements expected)))
    (make-typed-term :term tt.term
                     :path-cond tt.path-cond
                     :judgements (choose-judge tt.judgements tt.term
                                               to.supertype)))
  ///
  (more-returns
   (new-tt (implies (and (pseudo-termp expected)
                         (type-options-p options)
                         (equal (typed-term->kind tterm) 'variablep)
                         (good-typed-term-p tterm options))
                    (equal (typed-term->path-cond new-tt)
                           (typed-term->path-cond tterm)))
           :name unify-variable-maintains-path-cond)))

(define unify-quote ((tterm typed-term-p)
                     (expected pseudo-termp)
                     (options type-options-p))
  :guard (and (good-typed-term-p tterm options)
              (equal (typed-term->kind tterm) 'quotep))
  :returns (new-tt (good-typed-term-p new-tt options)
                   :hints (("Goal"
                            :in-theory (enable good-typed-quote-p))))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (pseudo-termp expected)
                          (equal (typed-term->kind tterm) 'quotep)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((type-options to) options)
       ((unless (is-conjunct-list? expected tt.term to.supertype))
        (prog2$
         (er hard? 'type-inference-topdown=>unify-variable
             "Expected ~p0 is not a conjunct list.~%" expected)
         tterm))
       ((unless (equal expected ''t))
        (make-typed-term :term tt.term
                         :path-cond tt.path-cond
                         :judgements expected)))
    (make-typed-term :term tt.term
                     :path-cond tt.path-cond
                     :judgements (choose-judge tt.judgements tt.term
                                               to.supertype)))
  ///
  (more-returns
   (new-tt (implies (and (pseudo-termp expected)
                         (equal (typed-term->kind tterm) 'quotep)
                         (good-typed-term-p tterm options))
                    (equal (typed-term->path-cond new-tt)
                           (typed-term->path-cond tterm)))
           :name unify-quote-maintains-path-cond)))

(defines unify-type
  :well-founded-relation l<
  :verify-guards nil
  :hints (("Goal"
           :in-theory (disable acl2-count implies-of-fncall-kind)))

  (define unify-fncall ((tterm typed-term-p)
                        (expected pseudo-termp)
                        (options type-options-p)
                        state)
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'fncallp))
    :returns (new-tt (good-typed-term-p new-tt options))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (pseudo-termp expected)
                            (equal (typed-term->kind tterm) 'fncallp)
                            (good-typed-term-p tterm options))))
          (make-typed-term))
         ((type-options to) options)
         ((typed-term tt) tterm)
         ((cons fn actuals) tt.term)
         (tt-actuals (typed-term-fncall->actuals tt to))
         (tta.path-cond (typed-term-list->path-cond tt-actuals))
         (tta.judgements (typed-term-list->judgements tt-actuals))
         ((typed-term ttt) (typed-term->top tt to))
         ;; for guard of make-typed-fncall
         ((unless (and (consp ttt.term)
                       (not (equal (car ttt.term) 'quote))))
          tt)
         (judge-top (if (equal expected ''t)
                        (choose-judge ttt.judgements ttt.term to.supertype)
                      expected))
         (new-top (make-typed-term :term ttt.term
                                   :path-cond ttt.path-cond
                                   :judgements judge-top))
         (conspair (assoc-equal fn to.functions))
         ((unless conspair)
          (prog2$
           (er hard? 'type-inference-topdown=>unify-fncall
               "There exists no function description for function ~p0. ~%" fn)
           tterm))
         (fn-description (cdr conspair))
         ((mv & returns-thms)
          (returns-judgement fn actuals actuals tta.judgements tta.judgements
                             fn-description tta.path-cond to.supertype ''t nil
                             state))
         (actuals-alst-try (choose-returns judge-top returns-thms fn actuals
                                           ttt.path-cond to t state))
         (actuals-alst (if actuals-alst-try actuals-alst-try
                         (choose-returns judge-top returns-thms fn actuals
                                         ttt.path-cond to nil state)))
         ((unless actuals-alst)
          (prog2$ (er hard? 'type-inference-topdown=>unify-fncall
                      "Run out of returns theorems, but returns judgement is not
                       covered. ~%")
                  tterm))
         (expected-actuals (get-actuals-judges actuals actuals-alst))
         (new-actuals (unify-type-list tt-actuals expected-actuals to state))
         ;; in order to satisfy the guards of make-typed-fncall
         ((unless (and (consp ttt.term)
                       (symbolp (car ttt.term))
                       (not (equal (car ttt.term) 'quote))
                       (not (equal (car ttt.term) 'if))
                       (equal (cdr ttt.term)
                              (typed-term-list->term-lst new-actuals))
                       (equal ttt.path-cond
                              (typed-term-list->path-cond new-actuals))))
          tt))
      (make-typed-fncall new-top new-actuals options)))

  (define unify-lambda ((tterm typed-term-p)
                        (expected pseudo-termp)
                        (options type-options-p)
                        state)
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'lambdap))
    :returns (new-tt (good-typed-term-p new-tt options))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (equal (typed-term->kind tterm) 'lambdap)
                            (good-typed-term-p tterm options))))
          (make-typed-term))
         ((type-options to) options)
         ((typed-term tt) tterm)
         (tt-actuals (typed-term-lambda->actuals tt to))
         ((typed-term tt-body) (typed-term-lambda->body tt to))
         ((typed-term tt-top) (typed-term->top tt to))
         (judge-top (if (equal expected ''t)
                        (choose-judge tt-top.judgements tt-top.term
                                      to.supertype)
                      expected))
         (new-top (make-typed-term :term tt-top.term
                                   :path-cond tt-top.path-cond
                                   :judgements judge-top))
         (body-expected
          (term-substitution judge-top `((,tt-top.term . ,tt-body.term)) t))
         (new-body (unify-type tt-body body-expected to state))
         ((typed-term nbd) new-body)
         (formals (lambda-formals (car tt-top.term)))
         (actuals (cdr tt-top.term))
         (formals-judges
          (look-up-judge-list formals nbd.judgements to.supertype))
         (actuals-expected
          (term-substitution-linear formals-judges formals actuals t))
         (new-actuals (unify-type-list tt-actuals actuals-expected options state)))
      (make-typed-lambda new-top new-body new-actuals to)))

  (define unify-if ((tterm typed-term-p)
                    (expected pseudo-termp)
                    (options type-options-p)
                    state)
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'ifp))
    :returns (new-tt (good-typed-term-p new-tt options))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp expected)
                            (type-options-p options)
                            (equal (typed-term->kind tterm) 'ifp)
                            (good-typed-term-p tterm options))))
          (make-typed-term))
         ((type-options to) options)
         ((typed-term tt) tterm)
         ((typed-term tt-cond) (typed-term-if->cond tt to))
         ((typed-term tt-then) (typed-term-if->then tt to))
         ((typed-term tt-else) (typed-term-if->else tt to))
         ((typed-term tt-top) (typed-term->top tt to))
         (new-cond (unify-type tt-cond ''t to state))
         (judge-top (if (equal expected ''t)
                        (choose-judge tt-top.judgements tt-top.term
                                      to.supertype)
                      expected))
         (new-top (make-typed-term :term tt-top.term
                                   :path-cond tt-top.path-cond
                                   :judgements judge-top))
         (then-expected (term-substitution judge-top `((,tt-top.term . ,tt-then.term)) t))
         (new-then (unify-type tt-then then-expected to state))
         (else-expected (term-substitution judge-top `((,tt-top.term . ,tt-else.term)) t))
         (new-else (unify-type tt-else else-expected to state)))
      (make-typed-if new-top new-cond new-then new-else to)))

  (define unify-type ((tterm typed-term-p)
                      (expected pseudo-termp)
                      (options type-options-p)
                      state)
    :guard (good-typed-term-p tterm options)
    :returns (new-tt (good-typed-term-p new-tt options))
    :measure (list (acl2-count (typed-term->term tterm)) 1)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (pseudo-termp expected)
                            (good-typed-term-p tterm options))))
          (make-typed-term))
         ((if (equal (typed-term->kind tterm) 'variablep))
          (unify-variable tterm expected options))
         ((if (equal (typed-term->kind tterm) 'quotep))
          (unify-quote tterm expected options))
         ((if (equal (typed-term->kind tterm) 'lambdap))
          (unify-lambda tterm expected options state))
         ((if (equal (typed-term->kind tterm) 'ifp))
          (unify-if tterm expected options state)))
      (unify-fncall tterm expected options state)))

  (define unify-type-list ((tterm-lst typed-term-list-p)
                           (expected-lst pseudo-term-listp)
                           (options type-options-p)
                           state)
    :returns (new-ttl (good-typed-term-list-p new-ttl options))
    :guard (good-typed-term-list-p tterm-lst options)
    :measure (list (acl2-count (typed-term-list->term-lst tterm-lst))
                   1)
    (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                            (type-options-p options)
                            (pseudo-term-listp expected-lst)
                            (good-typed-term-list-p tterm-lst options))))
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
         ((unless (equal (typed-term->path-cond tt-car)
                         (typed-term-list->path-cond tt-cdr)))
          tterm-lst))
      (cons tt-car tt-cdr)))
  ///
  (defthm typed-term-of-unify-fncall
    (typed-term-p (unify-fncall tterm expected options state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (unify-fncall tterm expected options state))
                              (options options))))))
  (defthm typed-term-of-unify-lambda
    (typed-term-p (unify-lambda tterm expected options state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (unify-lambda tterm expected options state))
                              (options options))))))
  (defthm typed-term-of-unify-if
    (typed-term-p (unify-if tterm expected options state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (unify-if tterm expected options state))
                              (options options))))))
  (defthm typed-term-of-unify-type
    (typed-term-p (unify-type tterm expected options state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-implies-typed-term)
             :use ((:instance good-typed-term-implies-typed-term
                              (tterm
                               (unify-type tterm expected options state))
                              (options options))))))
  (defthm typed-term-list-of-unify-type-list
    (typed-term-list-p (unify-type-list tterm-lst expected-lst options state))
    :hints (("Goal"
             :in-theory (disable good-typed-term-list-implies-typed-term-list)
             :use ((:instance good-typed-term-list-implies-typed-term-list
                              (tterm-lst
                               (unify-type-list tterm-lst expected-lst
                                                options state))
                              (options options))))))
  )

(verify-guards unify-type
  :hints (("Goal"
           :in-theory (enable make-typed-fncall-guard))))
