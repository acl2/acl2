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

(include-book "path-cond")
(include-book "evaluator")

(set-state-ok t)

;;-------------------------------------------------------
;;  Intersect judgements
(define intersect-judgements-acc ((judge1 pseudo-termp)
                                  (judge2 pseudo-termp)
                                  (acc pseudo-termp)
                                  state)
  :returns (intersect pseudo-termp)
  :verify-guards nil
  :measure (acl2-count (pseudo-term-fix judge2))
  (b* ((judge1 (pseudo-term-fix judge1))
       (judge2 (pseudo-term-fix judge2))
       (acc (pseudo-term-fix acc))
       ((if (and (not (is-conjunct? judge2))
                 (path-test judge1 judge2 state)))
        `(if ,judge2 ,acc 'nil))
       ((unless (is-conjunct? judge2)) acc)
       ((if (equal judge2 ''t)) acc)
       ((list & judge-hd judge-tl &) judge2)
       (acc-hd (intersect-judgements-acc judge1 judge-hd acc state)))
    (intersect-judgements-acc judge1 judge-tl acc-hd state)))

(verify-guards intersect-judgements-acc)

(defthm correctness-of-intersect-judgements-acc-judge1
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judge1)
                (pseudo-termp judge2)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp acc a)
                (ev-smtcp judge1 a))
           (ev-smtcp (intersect-judgements-acc judge1 judge2 acc state) a))
  :hints (("Goal"
           :in-theory (e/d (intersect-judgements-acc is-conjunct?)
                           (pseudo-termp
                            implies-of-is-conjunct?
                            acl2::pseudo-termp-opener
                            symbol-listp
                            consp-of-is-conjunct?
                            acl2::symbolp-of-car-when-symbol-listp
                            acl2::symbol-listp-of-cdr-when-symbol-listp)))))

(defthm correctness-of-intersect-judgements-acc-judge2
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judge1)
                (pseudo-termp judge2)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp acc a)
                (ev-smtcp judge2 a))
           (ev-smtcp (intersect-judgements-acc judge1 judge2 acc state) a))
  :hints (("Goal"
           :in-theory (e/d (intersect-judgements-acc is-conjunct?)
                           (pseudo-termp
                            implies-of-is-conjunct?
                            acl2::pseudo-termp-opener
                            symbol-listp
                            consp-of-is-conjunct?
                            acl2::symbolp-of-car-when-symbol-listp
                            acl2::symbol-listp-of-cdr-when-symbol-listp)))))

(define intersect-judgements ((judge1 pseudo-termp)
                              (judge2 pseudo-termp)
                              state)
  :returns (intersect pseudo-termp)
  (intersect-judgements-acc judge1 judge2 ''t state)
  ///
  (defthm correctness-of-intersect-judgements-judge1
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp judge1)
                  (pseudo-termp judge2)
                  (alistp a)
                  (ev-smtcp judge1 a))
             (ev-smtcp (intersect-judgements judge1 judge2 state) a))
    :hints (("Goal"
             :in-theory (enable intersect-judgements))))

  (defthm correctness-of-intersect-judgements-judge2
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp judge1)
                  (pseudo-termp judge2)
                  (alistp a)
                  (ev-smtcp judge2 a))
             (ev-smtcp (intersect-judgements judge1 judge2 state) a))
    :hints (("Goal"
             :in-theory (enable intersect-judgements)))))

#|
(defthm test (implies (integerp x) (rationalp x)))
(intersect-judgements '(if (rationalp x) (if (integerp x) 't 'nil) 'nil)
'(if (rationalp x) (if (integerp x) 't 'nil) 'nil)
state)

(intersect-judgements '(if (rationalp x) 't 'nil)
'(if (rationalp x) (if (integerp x) 't 'nil) 'nil)
state)
|#

;;------------------------------------------------------
;; Union judgements

(define union-judgements-acc ((judge1 pseudo-termp)
                              (judge2 pseudo-termp)
                              (acc pseudo-termp)
                              state)
  :returns (union pseudo-termp)
  :verify-guards nil
  :measure (acl2-count (pseudo-term-fix judge2))
  (b* ((judge1 (pseudo-term-fix judge1))
       (judge2 (pseudo-term-fix judge2))
       (acc (pseudo-term-fix acc))
       ((if (and (not (is-conjunct? judge2))
                 (not (path-test acc judge2 state))))
        `(if ,judge2 ,acc 'nil))
       ((unless (is-conjunct? judge2)) acc)
       ((if (equal judge2 ''t)) acc)
       ((list & judge-hd judge-tl &) judge2)
       (acc-hd (union-judgements-acc judge1 judge-hd acc state)))
    (union-judgements-acc judge1 judge-tl acc-hd state)))

(verify-guards union-judgements-acc)

(defthm correctness-of-union-judgements-acc
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judge1)
                (pseudo-termp judge2)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp acc a)
                (ev-smtcp judge1 a)
                (ev-smtcp judge2 a))
           (ev-smtcp (union-judgements-acc judge1 judge2 acc state) a))
  :hints (("Goal"
           :in-theory (e/d (union-judgements-acc is-conjunct?)
                           ()))))

(define union-judgements ((judge1 pseudo-termp)
                          (judge2 pseudo-termp)
                          state)
  :returns (union pseudo-termp)
  (union-judgements-acc judge1 judge2 judge1 state))

(defthm correctness-of-union-judgements
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judge1)
                (pseudo-termp judge2)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp judge1 a)
                (ev-smtcp judge2 a))
           (ev-smtcp (union-judgements judge1 judge2 state) a))
  :hints (("Goal"
           :in-theory (e/d (union-judgements)
                           ()))))


#|
(defthm test (implies (integerp x) (rationalp x)))
(union-judgements '(if (integerp x) 't 'nil)
'(if (rationalp x) (< x '0) 'nil)
state)
(union-judgements ''t
'(if (integerp x) (if (rationalp x) (< x '0) 'nil)
'nil)
state)
(union-judgements '(if (rationalp x) 't 'nil)
'(if (rationalp x) (if (integerp x) 't 'nil) 'nil)
state)
|#

;;-------------------------------------------------------
;; Super/subtype judgements

(encapsulate ()
  (local
   (in-theory (disable assoc-equal lambda-of-pseudo-lambdap symbol-listp
                       pseudo-term-listp-of-symbol-listp
                       acl2::symbol-listp-of-cdr-when-symbol-listp
                       consp-of-is-conjunct?
                       acl2::pseudo-lambdap-of-car-when-pseudo-lambda-listp
                       acl2::pseudo-lambda-listp-of-cdr-when-pseudo-lambda-listp
                       pseudo-lambdap-of-fn-call-of-pseudo-termp
                       nil-of-assoc-equal-of-pseudo-term-alistp
                       pseudo-term-alistp-when-not-consp
                       consp-of-pseudo-lambdap
                       acl2::pseudo-lambdap-of-car-when-pseudo-termp
                       acl2::pseudo-termp-list-cdr
                       pseudo-term-listp-of-cdr-of-pseudo-termp)))

(define construct-one-super/subtype ((type-judge pseudo-termp)
                                     (type-tuple type-tuple-p)
                                     (type-alst type-to-types-alist-p)
                                     (path-cond pseudo-termp)
                                     state)
  :ignore-ok t
  :returns (super/subtype-judge pseudo-termp)
  (b* ((type-judge (pseudo-term-fix type-judge))
       ((type-tuple tu) (type-tuple-fix type-tuple))
       (path-cond (pseudo-term-fix path-cond))
       (type-thm (acl2::meta-extract-formula-w tu.thm (w state)))
       ((unless (pseudo-termp type-thm))
        (prog2$
         (er hard? 'judgement-fns=>construct-one-super/subtype
             "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
             tu.thm type-thm)
         ''t))
       ((unless (type-predicate-p type-judge type-alst))
        (prog2$
         (er hard? 'judgement-fns=>construct-one-super/subtype
             "~p0 is not a type-predicate-p. Smtlink doesn't know how to ~
              calculate super/subtype for it.~%"
             type-judge)
         ''t))
       ((list root-type term) type-judge)
       ((unless (equal root-type tu.type))
        (prog2$
         (er hard? 'judgement-fns=>construct-one-super/subtype
             "The judgement's type ~p0 doesn't match the type-tuple's type ~
             ~p1~%" root-type tu.type)
         ''t))
       ((unless (equal (len tu.formals) 1))
        (prog2$
         (er hard? 'judgement-fns=>construct-one-super/subtype
             "The number of free variables in the type theorem must be one, ~
              but we find ~p0~%" tu.formals)
         ''t))
       (substed-thm
        (acl2::substitute-into-term type-thm `((,(car tu.formals) . ,term)))))
    (case-match substed-thm
      (('implies single-cond (!tu.neighbour-type !term))
       (if (or (equal tu.neighbour-type 'quote)
               (not (equal single-cond type-judge)))
           ''t
         (caddr substed-thm)))
      (('implies type-predicates (!tu.neighbour-type !term))
       (b* (((if (equal tu.neighbour-type 'quote)) ''t)
            ((unless (path-test-list `(if ,type-judge ,path-cond 'nil)
                                     type-predicates state))
             ''t))
         (caddr substed-thm)))
      (& ''t))))
)

(defthm my-substitute-into-term-correct
  (equal (ev-smtcp (acl2::substitute-into-term x subst) a)
         (ev-smtcp x (ev-smtcp-alist subst a)))
  :hints (("Goal"
           :in-theory (disable acl2::substitute-into-term-correct)
           :use ((:functional-instance
                  acl2::substitute-into-term-correct
                  (acl2::unify-ev ev-smtcp)
                  (acl2::unify-ev-lst ev-smtcp-lst)
                  (acl2::unify-ev-alist ev-smtcp-alist))))))

(encapsulate ()
  (local
   (defthm crock
     (implies (and (ev-smtcp-meta-extract-global-facts)
                   (pseudo-termp term)
                   (alistp a)
                   (consp term)
                   (consp (cdr term))
                   (consp (cddr term))
                   (equal (car term) 'implies)
                   (ev-smtcp term a)
                   (ev-smtcp (cadr term) a))
              (ev-smtcp (caddr term) a))))

(defthm correctness-of-construct-one-super/subtype
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp type-judge)
                (pseudo-termp path-cond)
                (alistp a)
                (ev-smtcp type-judge a)
                (ev-smtcp path-cond a))
           (ev-smtcp (construct-one-super/subtype
                      type-judge type-tuple type-alst path-cond state)
                     a))
  :hints (("Goal"
           :in-theory (e/d (construct-one-super/subtype)
                           (w
                            symbol-listp
                            pseudo-term-listp-of-symbol-listp
                            pseudo-term-listp
                            consp-of-is-conjunct?
                            acl2::pseudo-termp-car
                            acl2::symbol-listp-of-cdr-when-symbol-listp
                            pseudo-termp
                            correctness-of-path-test
                            consp-of-pseudo-lambdap
                            acl2::pseudo-termp-opener
                            ev-smtcp-of-booleanp-call
                            ev-smtcp-of-lambda
                            implies-of-is-conjunct?
                            ev-smtcp-meta-extract-formula
                            my-substitute-into-term-correct
                            crock
                            correctness-of-path-test-list
                            ))
           :do-not-induct t
           :use ((:instance ev-smtcp-meta-extract-formula
                            (name (type-tuple->thm type-tuple))
                            (st state)
                            (a (ev-smtcp-alist
                                (list (cons (car (type-tuple->formals type-tuple))
                                            (cadr type-judge)))
                                a)))
                 (:instance my-substitute-into-term-correct
                            (x (meta-extract-formula (type-tuple->thm type-tuple)
                                                                  state))
                            (subst (list (cons (car (type-tuple->formals type-tuple))
                                               (cadr type-judge))))
                            (a a))
                 (:instance crock
                            (term (acl2::substitute-into-term
                                   (meta-extract-formula (type-tuple->thm type-tuple)
                                                         state)
                                   (list (cons (car (type-tuple->formals type-tuple))
                                               (cadr type-judge)))))
                            (a a))
                 (:instance correctness-of-path-test-list
                            (path-cond (list* 'if type-judge path-cond '('nil)))
                            (expr-conj (cadr (acl2::substitute-into-term
                                              (meta-extract-formula (type-tuple->thm type-tuple)
                                                                    state)
                                              (list (cons (car (type-tuple->formals type-tuple))
                                                          (cadr type-judge))))))
                            (a a))
                 ))))
)

(define construct-closure ((type-judge pseudo-termp)
                           (super/subtype-tuple type-tuple-list-p)
                           (type-alst type-to-types-alist-p)
                           (path-cond pseudo-termp)
                           (acc pseudo-termp)
                           state)
  :returns (new-acc pseudo-termp)
  :measure (len super/subtype-tuple)
  (b* ((acc (pseudo-term-fix acc))
       (type-judge (pseudo-term-fix type-judge))
       (super/subtype-tuple (type-tuple-list-fix super/subtype-tuple))
       (path-cond (pseudo-term-fix path-cond))
       ((unless (consp super/subtype-tuple)) acc)
       ((cons first rest) super/subtype-tuple))
    (construct-closure type-judge rest type-alst path-cond
                       `(if ,(construct-one-super/subtype
                              type-judge first type-alst path-cond state)
                            ,acc
                          'nil)
                       state)))

(defthm correctness-of-construct-closure
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp type-judge)
                (type-tuple-list-p super/subtype-tuple)
                (pseudo-termp path-cond)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp type-judge a)
                (ev-smtcp path-cond a)
                (ev-smtcp acc a))
           (ev-smtcp (construct-closure
                      type-judge super/subtype-tuple
                      type-alst path-cond acc state)
                     a))
  :hints (("Goal"
           :in-theory (enable construct-closure))))

(defines super/subtype-transitive-closure
  :well-founded-relation l<
  :verify-guards nil
  :flag-local nil

  (define super/subtype ((type-judge pseudo-termp)
                         (path-cond pseudo-termp)
                         (type-alst type-to-types-alist-p)
                         (closure pseudo-termp)
                         (clock natp)
                         state)
    ;; clock is the length of the supertype-alst
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-fix type-judge)))
    :returns (closure pseudo-termp)
    (b* ((type-judge (pseudo-term-fix type-judge))
         (closure (pseudo-term-fix closure))
         (type-alst (type-to-types-alist-fix type-alst))
         (clock (nfix clock))
         ((if (zp clock)) closure)
         (exist? (look-up-path-cond type-judge closure type-alst))
         ((if exist?) closure)
         (new-closure `(if ,type-judge ,closure 'nil))
         ((unless (type-predicate-p type-judge type-alst)) new-closure)
         ((cons type &) type-judge)
         (item (assoc-equal type type-alst))
         ((unless item)
          (prog2$
           (er hard? 'type-inference-bottomup=>super/subtype
               "Type ~p0 doesn't exist in the supertype alist.~%" type)
           new-closure))
         ((unless (cdr item)) new-closure)
         (type-judge-lst
          (construct-closure type-judge (cdr item) type-alst path-cond
                             new-closure state)))
      (super/subtype-list type-judge-lst path-cond type-alst new-closure
                          (1- clock) state)))

  (define super/subtype-list ((type-judge-lst pseudo-termp)
                              (path-cond pseudo-termp)
                              (type-alst type-to-types-alist-p)
                              (closure pseudo-termp)
                              (clock natp)
                              state)
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-fix type-judge-lst)))
    :returns (closure pseudo-termp)
    (b* ((type-judge-lst (pseudo-term-fix type-judge-lst))
         (path-cond (pseudo-term-fix path-cond))
         (type-alst (type-to-types-alist-fix type-alst))
         (closure (pseudo-term-fix closure))
         (clock (nfix clock))
         ((unless (is-conjunct? type-judge-lst)) closure)
         ((if (equal type-judge-lst ''t)) closure)
         ((list & type-hd type-tl &) type-judge-lst)
         (new-closure
          (super/subtype type-hd path-cond type-alst closure clock state)))
      (super/subtype-list type-tl path-cond type-alst new-closure clock
                          state)))
  )

(verify-guards super/subtype)

#|
(super/subtype 'integerp '((integerp . (rationalp maybe-integerp))
(maybe-integerp . (maybe-rationalp))
(rationalp . (maybe-rationalp))
(maybe-rationalp . nil))
nil 4)

(super/subtype 'rationalp '((integerp . (rationalp maybe-integerp))
(maybe-integerp . (maybe-rationalp))
(rationalp . (maybe-rationalp))
(maybe-rationalp . nil))
nil 4)
|#

(encapsulate ()
  (local (in-theory (disable symbol-listp
                             pseudo-termp
                             pseudo-term-listp-of-symbol-listp
                             consp-of-is-conjunct?
                             acl2::symbol-listp-of-cdr-when-symbol-listp
                             acl2::symbol-listp-when-not-consp
                             consp-of-pseudo-lambdap
                             correctness-of-path-test-list
                             consp-of-cddr-of-pseudo-lambdap
                             ev-smtcp-of-variable)))

(defthm-super/subtype-transitive-closure-flag
  correctness-of-super/subtype-thms
  (defthm correctness-of-syper/subtype
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp type-judge)
                  (pseudo-termp path-cond)
                  (pseudo-termp closure)
                  (alistp a)
                  (ev-smtcp type-judge a)
                  (ev-smtcp path-cond a)
                  (ev-smtcp closure a))
             (ev-smtcp (super/subtype
                        type-judge path-cond type-alst
                        closure clock state)
                       a))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (super/subtype) ()))))
    :flag super/subtype)
  (defthm correctness-of-super/subtype-list
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp type-judge-lst)
                  (pseudo-termp path-cond)
                  (pseudo-termp closure)
                  (alistp a)
                  (ev-smtcp type-judge-lst a)
                  (ev-smtcp path-cond a)
                  (ev-smtcp closure a))
             (ev-smtcp (super/subtype-list
                        type-judge-lst path-cond type-alst
                        closure clock state)
                       a))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (super/subtype-list) ()))))
    :flag super/subtype-list))
)

(define super/subtype-judgements-acc ((judge pseudo-termp)
                                      (path-cond pseudo-termp)
                                      (type-alst type-to-types-alist-p)
                                      (acc pseudo-termp)
                                      state)
  :returns (judgements pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judge))
  :verify-guards nil
  (b* ((judge (pseudo-term-fix judge))
       (acc (pseudo-term-fix acc))
       ((if (type-predicate-p judge type-alst))
        (super/subtype judge path-cond type-alst acc (len type-alst) state))
       ((unless (is-conjunct? judge)) acc)
       ((if (equal judge ''t)) acc)
       ((list* & cond then &) judge)
       (first-acc
        (super/subtype-judgements-acc cond path-cond type-alst acc state)))
    (super/subtype-judgements-acc then path-cond type-alst first-acc state)))

(verify-guards super/subtype-judgements-acc)

(defthm correctness-of-super/subtype-judgements-acc
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judge)
                (pseudo-termp path-cond)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp judge a)
                (ev-smtcp path-cond a)
                (ev-smtcp acc a))
           (ev-smtcp (super/subtype-judgements-acc judge path-cond type-alst acc state)
                     a))
  :hints (("Goal"
           :in-theory (enable super/subtype-judgements-acc))))

(define super/subtype-judgements-fn ((judge pseudo-termp)
                                     (path-cond pseudo-termp)
                                     (type-alst type-to-types-alist-p)
                                     state)
  :returns (judgements pseudo-termp)
  (super/subtype-judgements-acc judge path-cond type-alst judge state))

(defthm correctness-of-super/subtype-judgements-fn
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judge)
                (pseudo-termp path-cond)
                (alistp a)
                (ev-smtcp judge a)
                (ev-smtcp path-cond a))
           (ev-smtcp (super/subtype-judgements-fn judge path-cond type-alst state)
                     a))
  :hints (("Goal"
           :in-theory (enable super/subtype-judgements-fn))))

#|
(defthm test (implies (integerp x) (rationalp x)))
(defoption maybe-integerp integerp :pred maybe-integerp)
(defthm test1 (implies (integerp x) (maybe-integerp x)))
(super/subtype-judgements-fn '(if (integerp x) 't 'nil) ''t
'((integerp . (rationalp maybe-integerp))
(rationalp . nil)
(maybe-integerp . nil))
'((((type . integerp) (neighbour-type . rationalp)) .
test)
(((type . integerp) (neighbour-type . maybe-integerp)) .
test1))
state)
|#

(defmacro super/subtype-judgements (judgements path-cond options state
                                               &key which)
  `(if (equal ,which :super)
       (super/subtype-judgements-fn ,judgements ,path-cond
                                    (type-options->supertype ,options)
                                    ,state)
     (super/subtype-judgements-fn ,judgements ,path-cond
                                  (type-options->subtype ,options)
                                  ,state)))

#|
(defthm test (implies (integerp x) (rationalp x)))
(super/subtype-judgements '(if (integerp x) 't 'nil) ''t
'((supertype (integerp rationalp)
(rationalp))
(supertype-thm (((type . integerp)
(neighbour-type . rationalp))
. test))
(subtype)
(subtype-thm)
(functions)
(consp)
(basic)
(list)
(alist)
(prod)
(option)
(sum)
(abstract))
state
:which :super)
|#

;; extend-judgements first calcualte the subtypes then it calculate the
;; supertypes based on the subtypes
(define extend-judgements ((judgements pseudo-termp)
                           (path-cond pseudo-termp)
                           (options type-options-p)
                           state)
  :returns (new-judgements pseudo-termp)
  (super/subtype-judgements
   (super/subtype-judgements judgements path-cond options state :which :sub)
   path-cond options state :which :super))

(defthm correctness-of-extend-judgements
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp judgements)
                (pseudo-termp path-cond)
                (alistp a)
                (ev-smtcp judgements a)
                (ev-smtcp path-cond a))
           (ev-smtcp (extend-judgements judgements path-cond options state) a))
  :hints (("Goal"
           :in-theory (enable extend-judgements))))
