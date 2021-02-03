;; Copyright (C) 2019, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "typed-term")
(include-book "judgement-fns")
(include-book "returns-judgement")

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

(define type-judgement-top-list ((judgements-lst pseudo-termp)
                                 (term-lst pseudo-term-listp)
                                 (options type-options-p))
  :returns (judgement-lst pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judgements-lst))
  (b* ((judgements-lst (pseudo-term-fix judgements-lst))
       (term-lst (pseudo-term-list-fix term-lst))
       ((unless (is-conjunct? judgements-lst))
        (er hard? 'type-inference-bottomup=>type-judgement-top-list
            "The top of type judgement is not a conjunction of conditions: ~q0"
            judgements-lst))
       ((if (or (equal judgements-lst ''t) (null term-lst))) ''t)
       ((list & judgements-hd judgements-tl &) judgements-lst)
       ((cons term-hd term-tl) term-lst))
    `(if ,(type-judgement-top judgements-hd term-hd options)
         ,(type-judgement-top-list judgements-tl term-tl options)
       'nil)))

;;-------------------------------------------------------
;; quoted judgements
;; nil judgements

(define type-judgement-nil-test ((supertype type-to-types-alist-p)
                                 (acc pseudo-termp)
                                 state)
  :returns (judgements pseudo-termp)
  :measure (len (type-to-types-alist-fix supertype))
  (b* ((supertype (type-to-types-alist-fix supertype))
       (acc (pseudo-term-fix acc))
       ((unless (consp supertype)) acc)
       ((cons (cons first-type &) rest) supertype)
       (term `(,first-type 'nil))
       ((mv err val) (partial-eval term nil state))
       ((if err) (type-judgement-nil-test rest acc state))
       ((if val) (type-judgement-nil-test rest `(if ,term ,acc 'nil) state)))
    (type-judgement-nil-test rest acc state)))

(define type-judgement-nil ((supertype type-to-types-alist-p) state)
  :returns (judgements pseudo-termp)
  (type-judgement-nil-test supertype ''t state))

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
       ((unless (mbt (acl2::fquotep term))) nil)
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
          (t (er hard? 'type-inference-bottomup=>type-judgement-quoted
                 "Type inference for constant term ~p0 is not supported.~%"
                 term)))))

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
    (extend-judgements judge-from-path-cond path-cond options state)))

;; ------------------------------------------------------------------
;;    The main type-judgements

(local
 (defthm pseudo-termp-of-lambda
   (implies (and (symbol-listp formals)
                 (pseudo-termp body-judgements)
                 (pseudo-term-listp actuals)
                 (equal (len formals) (len actuals)))
            (pseudo-termp `((lambda ,formals
                              ,body-judgements)
                            ,@actuals))))
 )

(defines type-judgements
  :well-founded-relation l<
  :verify-guards nil
  :hints (("Goal"
           :in-theory (disable
                       (:definition pseudo-termp)
                       (:rewrite acl2::pseudo-term-listp-of-cons)
                       nth symbol-listp assoc-equal)))
  :returns-hints
  (("Goal"
    :in-theory (disable
                (:definition pseudo-termp)
                (:rewrite acl2::pseudo-term-listp-of-cons)
                nth symbol-listp assoc-equal)))

  (define type-judgement-lambda ((term pseudo-termp)
                                 (path-cond pseudo-termp)
                                 (options type-options-p)
                                 state)
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    :guard (and (consp term)
                (pseudo-lambdap (car term)))
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         ((unless (mbt (and (consp term) (pseudo-lambdap (car term))))) nil)
         ((cons fn actuals) term)
         (formals (lambda-formals fn))
         (body (lambda-body fn))
         (shadowed-path-cond (shadow-path-cond formals path-cond))
         (actuals-judgements
          (type-judgement-list actuals path-cond options state))
         (substed-actuals-judgements
          (term-substitution actuals-judgements (pairlis$ actuals formals) t))
         (body-judgements
          (type-judgement body `(if ,shadowed-path-cond
                                    ,substed-actuals-judgements 'nil)
                          options state))
         (lambda-judgements
          `((lambda ,formals
              ,body-judgements)
            ,@actuals))
         (return-judgement
          (term-substitution (type-judgement-top body-judgements body options)
                             `((,body . ,term)) t)))
      `(if ,return-judgement
           (if ,lambda-judgements
               ,actuals-judgements
             'nil)
         'nil)))

  (define type-judgement-if ((term pseudo-termp)
                             (path-cond pseudo-termp)
                             (options type-options-p)
                             state)
    :guard (and (consp term)
                (equal (car term) 'if))
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         ((unless (mbt (and (consp term) (equal (car term) 'if)))) nil)
         ((cons & actuals) term)
         ((unless (equal (len actuals) 3))
          (er hard? 'type-inference-bottomup=>type-judgement-if
              "Mangled if term: ~q0" term))
         ((list cond then else) actuals)
         (judge-cond (type-judgement cond path-cond options state))
         (judge-then
          (type-judgement then `(if ,(simple-transformer cond) ,path-cond 'nil)
                          options state))
         (judge-else
          (type-judgement else
                          `(if ,(simple-transformer `(not ,cond)) ,path-cond 'nil)
                          options state))
         (judge-then-top (type-judgement-top judge-then then options))
         (judge-else-top (type-judgement-top judge-else else options))
         (judge-from-then (term-substitution judge-then-top `((,then . ,term)) t))
         (judge-from-else (term-substitution judge-else-top `((,else . ,term)) t))
         (judge-if-top (intersect-judgements judge-from-then judge-from-else
                                         state))
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
                             state)
    :guard (and (consp term)
                (symbolp (car term))
                (not (equal (car term) 'if))
                (not (equal (car term) 'quote)))
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         (options (type-options-fix options))
         ((unless (mbt (and (consp term)
                            (symbolp (car term))
                            (not (equal (car term) 'quote))
                            (not (equal (car term) 'if)))))
          nil)
         ((cons fn actuals) term)
         (actuals-judgements
          (type-judgement-list actuals path-cond options state))
         (actuals-judgements-top
          (type-judgement-top-list actuals-judgements actuals options))
         (functions (type-options->functions options))
         (conspair (assoc-equal fn functions))
         ((unless conspair)
          (er hard? 'type-inference-bottomup=>type-judgement-fn
              "There exists no function description for function ~p0. ~%" fn))
         (fn-description (cdr conspair))
         ;; return-judgement could be ''t which means it could be anything
         ((mv return-judgement &)
          (returns-judgement fn actuals actuals actuals-judgements-top
                             actuals-judgements-top fn-description path-cond
                             (type-options->supertype options) ''t nil state))
         ((if (equal return-judgement ''t))
          (er hard? 'type-inference-bottomup=>type-judgement-fn
              "Failed to find type judgements for return of function call ~
               ~p0~%" term))
         (return-judgement-extended
          (extend-judgements return-judgement path-cond options state)))
      `(if ,return-judgement-extended
           ,actuals-judgements
         'nil)))

  (define type-judgement ((term pseudo-termp)
                          (path-cond pseudo-termp)
                          (options type-options-p)
                          state)
    :measure (list (acl2-count (pseudo-term-fix term)) 1)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         (options (type-options-fix options))
         ((if (acl2::variablep term))
          (type-judgement-variable term path-cond options state))
         ((if (acl2::quotep term))
          (type-judgement-quoted term options state))
         ((cons fn &) term)
         ((if (pseudo-lambdap fn))
          (type-judgement-lambda term path-cond options state))
         ((if (equal fn 'if))
          (type-judgement-if term path-cond options state)))
      (type-judgement-fn term path-cond options state)))

  (define type-judgement-list ((term-lst pseudo-term-listp)
                               (path-cond pseudo-termp)
                               (options type-options-p)
                               state)
    :measure (list (acl2-count (pseudo-term-list-fix term-lst)) 1)
    :returns (judgements-lst pseudo-termp)
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (path-cond (pseudo-term-fix path-cond))
         ((unless (consp term-lst)) ''t)
         ((cons first rest) term-lst)
         (first-judge (type-judgement first path-cond options state))
         (rest-judge (type-judgement-list rest path-cond options state)))
      `(if ,first-judge
           ,rest-judge
         'nil)))
  )

(verify-guards type-judgement)

(define type-judge-cp ((cl pseudo-term-listp)
                       (hints t)
                       state)
  (b* (((unless (type-options-p hints)) (value cl))
       (goal (disjoin cl))
       (judges (type-judgement goal ''t hints state)))
    (value (list (list `(implies ,judges ,goal))))))

(local (in-theory (enable type-judge-cp)))

;; (skip-proofs
;;  (defthm correctness-of-type-judge-cp
;;    (implies (and (ev-smtcp-meta-extract-global-facts)
;;                  (pseudo-term-listp cl)
;;                  (alistp a)
;;                  (ev-smtcp
;;                   (conjoin-clauses
;;                    (acl2::clauses-result
;;                     (type-judge-cp cl hint state)))
;;                   a))
;;             (ev-smtcp (disjoin cl) a))
;;    :rule-classes :clause-processor)
;;  )
