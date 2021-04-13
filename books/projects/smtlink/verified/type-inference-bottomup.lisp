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

(include-book "basics")
(include-book "hint-please")
(include-book "typed-term-fns")
(include-book "judgement-fns")
(include-book "returns-judgement")
(include-book "../utils/fresh-vars")

(set-state-ok t)

;;-------------------------------------------------------
;; quoted judgements
;; nil judgements

(defthm ev-smtcp-of-fncall-with-nil
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (alistp a)
                (symbolp fn)
                (acl2::logicp fn (w state)))
           (equal (ev-smtcp (cons fn '('nil)) nil)
                  (ev-smtcp (cons fn '('nil)) a)))
  :hints (("Goal"
           :in-theory (disable ev-smtcp-of-fncall-args)
           :use ((:instance ev-smtcp-of-fncall-args
                            (x (cons fn '('nil)))
                            (a a))))))

(define type-judgement-nil-test ((supertype type-to-types-alist-p)
                                 (acc pseudo-termp)
                                 state)
  :returns (judgements pseudo-termp)
  :measure (len (type-to-types-alist-fix supertype))
  (b* ((supertype (type-to-types-alist-fix supertype))
       (acc (pseudo-term-fix acc))
       ((unless (consp supertype)) acc)
       ((cons (cons first-type &) rest) supertype)
       ((unless (acl2::logicp first-type (w state)))
        (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-nil-test
                    "~p0 is a program-mode function: ~q0" first-type)
                acc))
       (term `(,first-type 'nil))
       ((mv erp val) (magic-ev-fncall first-type '(nil) state t nil))
       ((if erp) (type-judgement-nil-test rest acc state))
       ((if val) (type-judgement-nil-test rest `(if ,term ,acc 'nil) state)))
    (type-judgement-nil-test rest acc state))
  ///
  (defthm correctness-of-type-judgement-nil-test
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (alistp a)
                  (pseudo-termp acc)
                  (type-to-types-alist-p supertype)
                  (ev-smtcp acc a))
             (ev-smtcp (type-judgement-nil-test supertype acc state)
                       a))))

(define type-judgement-nil ((supertype type-to-types-alist-p) state)
  :returns (judgements pseudo-termp)
  (type-judgement-nil-test supertype ''t state)
  ///
  (defthm correctness-of-type-judgement-nil
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (alistp a)
                  (type-to-types-alist-p supertype))
             (ev-smtcp (type-judgement-nil supertype state)
                       a))))

(define type-judgement-t ()
  :returns (judgements pseudo-termp)
  `(if (symbolp 't)
       (if (booleanp 't) 't 'nil)
     'nil))

(define type-judgement-quoted ((term pseudo-termp)
                               (options type-options-p)
                               state)
  :guard (and (not (acl2::variablep term))
              (acl2::fquotep term))
  :returns (judgements pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (options (type-options-fix options))
       ((unless (mbt (acl2::fquotep term))) ''t)
       (const (cadr term)))
    (cond ((integerp const)
           (extend-judgements `(if (integerp ',const) 't 'nil) ''t options state))
          ((rationalp const)
           (extend-judgements `(if (rationalp ',const) 't 'nil) ''t options state))
          ((equal const t)
           (extend-judgements (type-judgement-t) ''t options state))
          ((null const)
           (type-judgement-nil (type-options->supertype options) state))
          ((symbolp const)
           (extend-judgements `(if (symbolp ',const) 't 'nil) ''t options state))
          (t (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-quoted
                         "Type inference for constant term ~p0 is not supported.~%"
                         term)
                     ''t))))
  ///
  (defthm correctness-of-type-judgement-quoted
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (alistp a))
             (ev-smtcp (type-judgement-quoted term options state) a))))

;; ------------------------------------------------------------------
;;    Variable judgements

(define type-judgement-variable ((term pseudo-termp)
                                 (path-cond pseudo-termp)
                                 (options type-options-p)
                                 state)
  :returns (judgements pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (path-cond (pseudo-term-fix path-cond))
       (options (type-options-fix options))
       (supertype (type-options->supertype options))
       (judge-from-path-cond (look-up-path-cond term path-cond supertype)))
    (extend-judgements judge-from-path-cond path-cond options state))
  ///
  (defthm correctness-of-type-judgement-variable
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (pseudo-termp path-cond)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (type-judgement-variable term path-cond options state) a))))

;; ------------------------------------------------------------------
;;    The main type-judgements

(define type-judgement-if-top ((judge-then pseudo-termp)
                               (then pseudo-termp)
                               (judge-else pseudo-termp)
                               (else pseudo-termp)
                               (cond pseudo-termp)
                               (names symbol-listp)
                               (options type-options-p))
  :returns (judge-if-top pseudo-termp)
  (b* ((judge-then (pseudo-term-fix judge-then))
       (then (pseudo-term-fix then))
       (judge-else (pseudo-term-fix judge-else))
       (else (pseudo-term-fix else))
       (names (symbol-list-fix names))
       (options (type-options-fix options))
       (supertype-alst (type-options->supertype options))
       (new-var (new-fresh-var names))
       ((mv fast-else &)
        (make-fast-judgements judge-else else new-var
                              supertype-alst nil 0))
       (ind-lst
        (map-judgements judge-then then new-var supertype-alst fast-else))
       ((mv judge-then-common &)
        (construct-judge-by-list judge-then then
                                 supertype-alst ind-lst ''t))
       (judge-else-common
        (construct-judge-by-find judge-else else supertype-alst ind-lst ''t))
       (judge `(if ,cond ,judge-then-common ,judge-else-common)))
    (merge-if-judgements (rearrange-if-judgements judge) then else supertype-alst)))

(defthm correctness-of-type-judgement-if-top
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judge-then)
                (pseudo-termp then)
                (pseudo-termp judge-else)
                (pseudo-termp else)
                (pseudo-termp cond)
                (alistp a)
                (ev-smtcp `(if ,cond ,judge-then ,judge-else) a))
           (ev-smtcp (type-judgement-if-top judge-then then judge-else else
                                            cond names options)
                     a))
  :hints (("Goal"
           :in-theory (e/d (type-judgement-if-top)
                           (correctness-of-path-test-list
                            correctness-of-path-test
                            consp-of-pseudo-lambdap
                            pseudo-termp)))))

(define generate-judge-from-equality-acc ((lhs symbolp)
                                          (rhs pseudo-termp)
                                          (judge pseudo-termp)
                                          (supertype-alst
                                           type-to-types-alist-p)
                                          (acc pseudo-termp))
  :returns (new-judge pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judge))
  :verify-guards nil
  (b* ((lhs (pseudo-term-fix lhs))
       (rhs (pseudo-term-fix rhs))
       (judge (pseudo-term-fix judge))
       (acc (pseudo-term-fix acc))
       ((if (equal judge ''t)) acc)
       ((if (judgement-of-term judge rhs supertype-alst))
        `(if ,(substitute-term-in-judge judge rhs lhs supertype-alst) ,acc 'nil))
       ((unless (is-conjunct? judge)) acc)
       ((list* & judge-hd judge-tl &) judge)
       (new-acc (generate-judge-from-equality-acc lhs rhs judge-hd
                                                  supertype-alst acc)))
    (generate-judge-from-equality-acc lhs rhs judge-tl supertype-alst
                                      new-acc)))

(verify-guards generate-judge-from-equality-acc)

(defthm correctness-of-generate-judge-from-equality-acc
  (implies (and (symbolp lhs)
                (pseudo-termp rhs)
                (pseudo-termp judge)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp judge a)
                (ev-smtcp acc a)
                (equal (ev-smtcp lhs a) (ev-smtcp rhs a)))
           (ev-smtcp (generate-judge-from-equality-acc
                      lhs rhs judge supertype-alst acc)
                     a))
  :hints (("Goal"
           :induct (generate-judge-from-equality-acc
                    lhs rhs judge supertype-alst acc)
           :in-theory (e/d (generate-judge-from-equality-acc is-conjunct?)
                           (implies-of-is-conjunct?
                            member-equal symbol-listp
                            consp-of-is-conjunct?
                            correctness-of-path-test-list
                            correctness-of-path-test
                            consp-of-pseudo-lambdap)))))

(define generate-judge-from-equality ((lhs symbolp)
                                      (rhs pseudo-termp)
                                      (judge pseudo-termp)
                                      (supertype-alst type-to-types-alist-p))
  :returns (new-judge pseudo-termp)
  (generate-judge-from-equality-acc lhs rhs judge supertype-alst ''t))

(defthm correctness-of-generate-judge-from-equality
  (implies (and (symbolp lhs)
                (pseudo-termp rhs)
                (pseudo-termp judge)
                (alistp a)
                (ev-smtcp judge a)
                (equal (ev-smtcp lhs a) (ev-smtcp rhs a)))
           (ev-smtcp (generate-judge-from-equality lhs rhs judge
                                                   supertype-alst)
                     a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (generate-judge-from-equality) ()))))

(define augment-path-cond ((cond pseudo-termp)
                           (judge-cond pseudo-termp)
                           (path-cond pseudo-termp)
                           (supertype-alst type-to-types-alist-p))
  :returns (mv (then-pc pseudo-termp)
               (else-pc pseudo-termp))
  (b* ((cond (pseudo-term-fix cond))
       (judge-cond (pseudo-term-fix judge-cond))
       (path-cond (pseudo-term-fix path-cond))
       ((mv okp1 var1 term1)
        (case-match cond
          (('equal lhs rhs) (mv (symbolp lhs) lhs rhs))
          (& (mv nil nil nil))))
       ((mv okp2 var2 term2)
        (case-match cond
          (('not ('equal lhs rhs)) (mv (symbolp lhs) lhs rhs))
          (& (mv nil nil nil))))
       ((unless (or okp1 okp2))
        (mv (conjoin `(,(simple-transformer cond) ,path-cond))
            (conjoin `(,(simple-transformer `(not ,cond)) ,path-cond))))
       ((if okp1)
        (mv (conjoin `(,(generate-judge-from-equality var1 term1 judge-cond
                                                      supertype-alst)
                       ,(simple-transformer cond) ,path-cond))
            (conjoin `(,(simple-transformer `(not ,cond)) ,path-cond)))))
    (mv (conjoin `(,(simple-transformer cond) ,path-cond))
        (conjoin `(,(generate-judge-from-equality var2 term2 judge-cond
                                                  supertype-alst)
                   ,(simple-transformer `(not ,cond)) ,path-cond)))))

(defthm correctness-of-augment-path-cond-1
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp cond)
                (pseudo-termp judge-cond)
                (pseudo-termp path-cond)
                (alistp a)
                (ev-smtcp judge-cond a))
           (b* (((mv then-pc &)
                 (augment-path-cond cond judge-cond path-cond supertype-alst)))
             (iff (ev-smtcp then-pc a)
                  (ev-smtcp `(if ,cond ,path-cond 'nil) a))))
  :hints (("Goal"
           :in-theory (e/d (augment-path-cond simple-transformer)
                           (pseudo-termp
                            correctness-of-path-test-list-corollary
                            correctness-of-path-test-list
                            correctness-of-path-test
                            symbol-listp
                            acl2::symbol-listp-when-not-consp
                            ev-smtcp-of-variable
                            consp-of-is-conjunct?
                            acl2::pseudo-termp-opener)))))

(defthm correctness-of-augment-path-cond-2
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp cond)
                (pseudo-termp judge-cond)
                (pseudo-termp path-cond)
                (alistp a)
                (ev-smtcp judge-cond a))
           (b* (((mv & else-pc)
                 (augment-path-cond cond judge-cond path-cond supertype-alst)))
             (iff (ev-smtcp else-pc a)
                  (ev-smtcp `(if (not ,cond) ,path-cond 'nil) a))))
  :hints (("Goal"
           :in-theory (e/d (augment-path-cond simple-transformer)
                           (pseudo-termp
                            correctness-of-path-test-list-corollary
                            correctness-of-path-test-list
                            correctness-of-path-test
                            symbol-listp
                            acl2::symbol-listp-when-not-consp
                            ev-smtcp-of-variable
                            consp-of-is-conjunct?
                            acl2::pseudo-termp-opener)))))

(defines type-judgements
  :flag-local nil
  :well-founded-relation l<
  :verify-guards nil

  (define type-judgement-if ((term pseudo-termp)
                             (path-cond pseudo-termp)
                             (options type-options-p)
                             (names symbol-listp)
                             state)
    :guard (and (consp term)
                (equal (car term) 'if))
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         (names (symbol-list-fix names))
         (options (type-options-fix options))
         ((type-options o) options)
         ((unless (mbt (and (consp term) (equal (car term) 'if)))) ''t)
         ((cons & actuals) term)
         ((unless (equal (len actuals) 3))
          (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-if
                      "Mangled if term: ~q0" term)
                  ''t))
         ((list cond then else) actuals)
         (judge-cond (type-judgement cond path-cond options names state))
         ((mv then-path-cond else-path-cond)
          (augment-path-cond cond judge-cond path-cond o.supertype))
         (judge-then
          (type-judgement then then-path-cond options names state))
         (judge-else
          (type-judgement else else-path-cond options names state))
         (judge-then-top (type-judgement-top judge-then then options))
         (judge-else-top (type-judgement-top judge-else else options))
         (judge-if-top
          (type-judgement-if-top judge-then-top then judge-else-top else
                                 cond names options))
         (judge-if-top-extended
          (extend-judgements judge-if-top path-cond options state)))
      `(if ,judge-if-top-extended
           (if ,judge-cond
               (if ,cond ,judge-then ,judge-else)
             'nil)
         'nil)))

  (define type-judgement-fn ((term pseudo-termp)
                             (path-cond pseudo-termp)
                             (options type-options-p)
                             (names symbol-listp)
                             state)
    :guard (and (consp term)
                (symbolp (car term))
                (not (equal (car term) 'if))
                (not (equal (car term) 'quote)))
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         (names (symbol-list-fix names))
         (options (type-options-fix options))
         ((unless (mbt (and (consp term)
                            (symbolp (car term))
                            (not (equal (car term) 'quote))
                            (not (equal (car term) 'if)))))
          ''t)
         ((cons fn actuals) term)
         (actuals-judgements
          (type-judgement-list actuals path-cond options names state))
         (actuals-judgements-top
          (type-judgement-top-list actuals-judgements actuals options))
         (functions (type-options->functions options))
         (conspair (assoc-equal fn functions))
         ((unless conspair)
          (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-fn
                      "There exists no function description for function ~p0. ~
                       ~%" fn)
                  ''t))
         (fn-description (cdr conspair))
         ;; return-judgement could be ''t which means it could be anything
         (return-judgement
          (returns-judgement fn actuals actuals-judgements-top fn-description
                             path-cond ''t state))
         ((if (equal return-judgement ''t))
          (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-fn
                      "Failed to find type judgements for return of function ~
                       call ~p0~%Current path-cond: ~p1~%Actuals-judgements: ~
                       ~p2~%"
                      term path-cond actuals-judgements-top)
                  ''t))
         (return-judgement-extended
          (extend-judgements return-judgement path-cond options state)))
      `(if ,return-judgement-extended
           ,actuals-judgements
         'nil)))

  (define type-judgement ((term pseudo-termp)
                          (path-cond pseudo-termp)
                          (options type-options-p)
                          (names symbol-listp)
                          state)
    :measure (list (acl2-count (pseudo-term-fix term)) 1)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         (names (symbol-list-fix names))
         (options (type-options-fix options))
         ((if (acl2::variablep term))
          (type-judgement-variable term path-cond options state))
         ((if (acl2::quotep term))
          (type-judgement-quoted term options state))
         ((cons fn &) term)
         ((if (pseudo-lambdap fn))
          ;; (type-judgement-lambda term path-cond options names state)
          (prog2$ (er hard? 'type-inference-bottomup=>type-judgement
                      "Found lambda in the goal.~%")
                  ''t))
         ((if (equal fn 'if))
          (type-judgement-if term path-cond options names state)))
      (type-judgement-fn term path-cond options names state)))

  (define type-judgement-list ((term-lst pseudo-term-listp)
                               (path-cond pseudo-termp)
                               (options type-options-p)
                               (names symbol-listp)
                               state)
    :measure (list (acl2-count (pseudo-term-list-fix term-lst)) 1)
    :returns (judgements-lst pseudo-termp)
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (path-cond (pseudo-term-fix path-cond))
         (names (symbol-list-fix names))
         ((unless (consp term-lst)) ''t)
         ((cons first rest) term-lst)
         (first-judge (type-judgement first path-cond options names state))
         (rest-judge (type-judgement-list rest path-cond options names state)))
      `(if ,first-judge
           ,rest-judge
         'nil)))
  ///
  (defthm correctness-of-type-judgement-list-nil
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp path-cond)
                  (symbol-listp names)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (type-judgement-list nil path-cond options names state) a))
    :hints (("Goal"
             :expand (type-judgement-list nil path-cond options names state))))
  )

(verify-guards type-judgement)

;; ------------------------------------------------
;; Correctness theorems for type-judgement

(defthm-type-judgements-flag
  (defthm correctness-of-type-judgement-if
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (pseudo-termp path-cond)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (type-judgement-if term path-cond options names state) a))
    :flag type-judgement-if
    :hints ((and stable-under-simplificationp
                 '(:in-theory (disable
                               pseudo-termp
                               correctness-of-path-test-list
                               symbol-listp
                               correctness-of-path-test
                               acl2::symbol-listp-when-not-consp
                               consp-of-is-conjunct?
                               acl2::pseudo-termp-cadr-from-pseudo-term-listp
                               acl2::symbolp-of-car-when-symbol-listp
                               pseudo-term-listp-of-symbol-listp
                               acl2::pseudo-termp-opener)
                              :expand (type-judgement-if term path-cond options
                                                         names state)))))
  (defthm correctness-of-type-judgement-fn
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (pseudo-termp path-cond)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (type-judgement-fn term path-cond options names state) a))
    :hints ((and stable-under-simplificationp
                 '(:expand (type-judgement-fn term path-cond options names
                                              state))))
    :flag type-judgement-fn)
  (defthm correctness-of-type-judgement
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (pseudo-termp path-cond)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (type-judgement term path-cond options names state) a))
    :flag type-judgement
    :hints ((and stable-under-simplificationp
                 '(:expand (type-judgement term path-cond options names
                                           state)))))
  (defthm correctness-of-type-judgement-list
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-term-listp term-lst)
                  (pseudo-termp path-cond)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (type-judgement-list term-lst path-cond options names state)
                       a))
    :hints ((and stable-under-simplificationp
                 '(:expand ((type-judgement-list term-lst path-cond options
                                                 names state)
                            (type-judgement-list nil path-cond options names state)))))
    :flag type-judgement-list)
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

;; -------------------------------------------------------

(define type-judge-bottomup-cp ((cl pseudo-term-listp)
                                (hints t)
                                state)
  (b* (((unless (type-inference-hints-p hints))
        (value (list cl)))
       ((type-inference-hints h) hints)
       (goal (disjoin cl))
       (judges (type-judgement goal ''t h.type-options h.names state)))
    (value (list (list `(implies ,judges ,goal))))))

(local (in-theory (enable type-judge-bottomup-cp)))

(defthm correctness-of-type-judge-bottomup-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (type-judge-bottomup-cp cl hints state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :rule-classes :clause-processor)
