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
;; ------------------------------------------------------------
;; Return the topest judgement

(define type-judgement-top ((judgements pseudo-termp)
                            (term pseudo-termp)
                            (options type-options-p))
  :returns (judgement pseudo-termp)
  (b* ((judgements (pseudo-term-fix judgements))
       (options (type-options-fix options))
       (supertype-alst (type-options->supertype options)))
    (look-up-path-cond term judgements supertype-alst)))

(defthm correctness-of-type-judgement-top
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp term)
                (pseudo-termp judgements)
                (alistp a)
                (ev-smtcp judgements a))
           (ev-smtcp (type-judgement-top judgements term options) a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable type-judgement-top))))

(define type-judgement-top-list ((judgements-lst pseudo-termp)
                                 (term-lst pseudo-term-listp)
                                 (options type-options-p))
  :returns (judgement-lst pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judgements-lst))
  (b* ((judgements-lst (pseudo-term-fix judgements-lst))
       (term-lst (pseudo-term-list-fix term-lst))
       ((unless (is-conjunct? judgements-lst))
        (prog2$
         (er hard? 'type-inference-bottomup=>type-judgement-top-list
             "The top of type judgement is not a conjunction of conditions: ~q0"
             judgements-lst)
         ''t))
       ((if (or (equal judgements-lst ''t) (null term-lst))) ''t)
       ((list & judgements-hd judgements-tl &) judgements-lst)
       ((cons term-hd term-tl) term-lst))
    `(if ,(type-judgement-top judgements-hd term-hd options)
         ,(type-judgement-top-list judgements-tl term-tl options)
       'nil)))

(defthm correctness-of-type-judgement-top-list
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp term-lst)
                (pseudo-termp judgements-lst)
                (alistp a)
                (ev-smtcp judgements-lst a))
           (ev-smtcp (type-judgement-top-list judgements-lst term-lst options) a))
  :hints (("Goal"
           :in-theory (enable type-judgement-top-list))))

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

;; (local
;;  (defthm pseudo-termp-of-lambda
;;    (implies (and (symbol-listp formals)
;;                  (pseudo-termp body-judgements)
;;                  (pseudo-term-listp actuals)
;;                  (equal (len formals) (len actuals)))
;;             (pseudo-termp `((lambda ,formals
;;                               ,body-judgements)
;;                             ,@actuals))))
;;  )

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
        (map-judgements judge-then then new-var
                        supertype-alst fast-else nil))
       ((mv judge-then-common &)
        (construct-judge-by-list judge-then then
                                 supertype-alst ind-lst ''t))
       ((mv judge-else-common &)
        (construct-judge-by-find judge-then then judge-else else
                                 supertype-alst ind-lst ''t))
       (judge `(if ,cond ,judge-then-common ,judge-else-common)))
    (merge-if-judgements judge then else supertype-alst)))

(defthm correctness-of-type-judgement-if-top
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judge-then)
                (pseudo-termp then)
                (pseudo-termp judge-else)
                (pseudo-termp else)
                (pseudo-termp cond)
                (symbol-listp names)
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

(defines type-judgements
  :flag-local nil
  :well-founded-relation l<
  :verify-guards nil

  ;; (define type-judgement-lambda ((term pseudo-termp)
  ;;                                (path-cond pseudo-termp)
  ;;                                (options type-options-p)
  ;;                                (names symbol-listp)
  ;;                                state)
  ;;   :measure (list (acl2-count (pseudo-term-fix term)) 0)
  ;;   :guard (and (consp term)
  ;;               (pseudo-lambdap (car term)))
  ;;   :returns (judgements pseudo-termp)
  ;;   (b* ((term (pseudo-term-fix term))
  ;;        (path-cond (pseudo-term-fix path-cond))
  ;;        (names (symbol-list-fix names))
  ;;        ((unless (mbt (and (consp term) (pseudo-lambdap (car term))))) ''t)
  ;;        ((cons fn actuals) term)
  ;;        (formals (lambda-formals fn))
  ;;        (body (lambda-body fn))
  ;;        ;; (shadowed-path-cond (shadow-path-cond formals path-cond))
  ;;        (actuals-judgements
  ;;         (type-judgement-list actuals path-cond options names state))
  ;;        (formals-judgements
  ;;         (term-substitution actuals-judgements (pairlis$ actuals formals) t))
  ;;        (body-judgements
  ;;         (type-judgement body formals-judgements options names state))
  ;;        (lambda-judgements
  ;;         `((lambda ,formals
  ;;             ,body-judgements)
  ;;           ,@actuals))
  ;;        (return-judgement
  ;;         (term-substitution (type-judgement-top body-judgements body options)
  ;;                            `((,body . ,term)) t)))
  ;;     `(if ,return-judgement
  ;;          (if ,lambda-judgements
  ;;              ,actuals-judgements
  ;;            'nil)
  ;;        'nil)))

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
         ((unless (mbt (and (consp term) (equal (car term) 'if)))) ''t)
         ((cons & actuals) term)
         ((unless (equal (len actuals) 3))
          (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-if
                      "Mangled if term: ~q0" term)
                  ''t))
         ((list cond then else) actuals)
         (judge-cond (type-judgement cond path-cond options names state))
         (judge-then
          (type-judgement then `(if ,(simple-transformer cond) ,path-cond 'nil)
                          options names state))
         (judge-else
          (type-judgement else
                          `(if ,(simple-transformer `(not ,cond)) ,path-cond 'nil)
                          options names state))
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
         ((mv return-judgement &)
          (returns-judgement fn actuals actuals actuals-judgements-top
                             actuals-judgements-top fn-description path-cond
                             (type-options->supertype options) ''t nil state))
         ((if (equal return-judgement ''t))
          (prog2$ (er hard? 'type-inference-bottomup=>type-judgement-fn
                      "Failed to find type judgements for return of function ~
                       call ~p0~%" term)
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
  ;; (defthm correctness-of-type-judgement-lambda
  ;;   (implies (and (ev-smtcp-meta-extract-global-facts)
  ;;                 (pseudo-termp term)
  ;;                 (pseudo-termp path-cond)
  ;;                 (alistp a)
  ;;                 (ev-smtcp path-cond a))
  ;;            (ev-smtcp (type-judgement-lambda term path-cond options state) a))
  ;;   :flag type-judgement-lambda
  ;;   :hints ((and stable-under-simplificationp
  ;;                '(:expand (type-judgement-lambda term path-cond options state)))))
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

(define type-judge-cp ((cl pseudo-term-listp)
                       (hints t)
                       state)
  (b* (((unless (type-inference-hints-p hints))
        (value (list cl)))
       ((type-inference-hints h) hints)
       (goal (disjoin cl))
       (judges (type-judgement goal ''t h.type-options h.names state)))
    (value (list (list `(implies ,judges ,goal))))))

(local (in-theory (enable type-judge-cp)))

(defthm correctness-of-type-judge-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (type-judge-cp cl hints state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :rule-classes :clause-processor)
