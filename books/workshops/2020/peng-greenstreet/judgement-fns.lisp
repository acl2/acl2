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

(include-book "path-cond")

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

(define intersect-judgements ((judge1 pseudo-termp)
                          (judge2 pseudo-termp)
                          state)
  :returns (intersect pseudo-termp)
  (intersect-judgements-acc judge1 judge2 ''t state))

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

(define union-judgements ((judge1 pseudo-termp)
                          (judge2 pseudo-termp)
                          state)
  :returns (union pseudo-termp)
  (union-judgements-acc judge1 judge2 judge1 state))

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

(defines super/subtype-transitive-closure
  :well-founded-relation l<
  :verify-guards nil
  :hints (("Goal" :in-theory (disable pseudo-termp symbol-listp)))

  (define super/subtype ((type symbolp)
                         (type-alst type-to-types-alist-p)
                         (closure symbol-listp)
                         (clock natp)) ;; clock is the length of the supertype-alst
    :measure (list (nfix clock) (acl2-count (symbol-fix type)))
    :returns (closure symbol-listp)
    (b* ((type (symbol-fix type))
         (type-alst (type-to-types-alist-fix type-alst))
         (closure (symbol-list-fix closure))
         (clock (nfix clock))
         ((if (zp clock)) closure)
         (exist? (member-equal type closure))
         ((if exist?) closure)
         (new-closure (cons type closure))
         (item (assoc-equal type type-alst))
         ((unless item)
          (er hard? 'type-inference-bottomup=>super/subtype
              "Type ~p0 doesn't exist in the supertype alist.~%" type))
         ((unless (cdr item)) new-closure)
         (type-lst (cdr item)))
      (super/subtype-list type-lst type-alst new-closure (1- clock))))

  (define super/subtype-list ((type-lst symbol-listp)
                              (type-alst type-to-types-alist-p)
                              (closure symbol-listp)
                              (clock natp))
    :measure (list (nfix clock) (acl2-count (symbol-list-fix type-lst)))
    :returns (closure symbol-listp)
    (b* ((type-lst (symbol-list-fix type-lst))
         (type-alst (type-to-types-alist-fix type-alst))
         (closure (symbol-list-fix closure))
         (clock (nfix clock))
         ((unless (consp type-lst)) closure)
         ((cons type-hd type-tl) type-lst)
         (new-closure (super/subtype type-hd type-alst closure clock)))
      (super/subtype-list type-tl type-alst new-closure clock)))
  )

(verify-guards super/subtype
  :hints (("Goal" :in-theory (disable pseudo-termp
                                      consp-of-is-conjunct?))))

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

(local
 (defthm pseudo-termp-of-cadr-of-consp
   (implies (and (pseudo-termp x)
                 (not (equal (car x) 'quote))
                 (consp x)
                 (consp (cdr x)))
            (pseudo-termp (cadr x)))
   :hints (("Goal" :in-theory (enable pseudo-termp)))))

(define look-up-type-tuple-to-thm-alist ((root-type symbolp)
                                         (type symbolp)
                                         (thms type-tuple-to-thm-alist-p)
                                         (term pseudo-termp)
                                         (path-cond pseudo-termp)
                                         state)
  :returns (ok booleanp)
  :guard-hints (("Goal"
                 :in-theory (disable assoc-equal
                                     symbol-listp
                                     pseudo-term-listp-of-cdr-of-pseudo-termp
                                     default-cdr
                                     consp-of-pseudo-lambdap)))
  :ignore-ok t
  (b* ((thms (type-tuple-to-thm-alist-fix thms))
       (path-cond (pseudo-term-fix path-cond))
       (term (pseudo-term-fix term))
       (tuple (make-type-tuple :type root-type
                               :neighbour-type type))
       (conspair (assoc-equal tuple thms))
       ((unless conspair) nil)
       (thm-name (cdr conspair))
       (type-thm
        (acl2::meta-extract-formula-w thm-name (w state)))
       ((unless (pseudo-termp type-thm))
        (er hard? 'type-inference-bottomup=>look-up-type-tuple-to-thm-alist
            "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
            thm-name type-thm))
       (ok (case-match type-thm
             (('implies (!root-type var) (!type var)) t)
             (('implies type-predicates (!type var))
              (b* (((if (equal type 'quote)) nil)
                   (substed (term-substitution type-predicates `((,var . ,term)) t)))
                (path-test-list `(if (,root-type ,term) ,path-cond 'nil)
                                substed state)))
             (& nil))))
    ok))

(encapsulate ()
  (local (in-theory (disable (:definition pseudo-termp)
                             (:rewrite lambda-of-pseudo-lambdap))))
  (local
   (defthm assoc-equal-of-type-tuple-to-thm-alist-p
     (implies (and (type-tuple-to-thm-alist-p x)
                   (assoc-equal y x))
              (and (consp (assoc-equal y x))
                   (symbolp (cdr (assoc-equal y x)))))))

(define super/subtype-to-judgements ((root-type symbolp)
                                     (types symbol-listp)
                                     (term pseudo-termp)
                                     (thms type-tuple-to-thm-alist-p)
                                     (path-cond pseudo-termp)
                                     (acc pseudo-termp)
                                     state)
  :returns (judgements pseudo-termp)
  :measure (len types)
  (b* ((root-type (symbol-fix root-type))
       (types (symbol-list-fix types))
       (term (pseudo-term-fix term))
       (thms (type-tuple-to-thm-alist-fix thms))
       (acc (pseudo-term-fix acc))
       ((unless (consp types)) acc)
       ((cons types-hd types-tl) types)
       ((if (equal root-type types-hd))
        (super/subtype-to-judgements root-type types-tl term thms path-cond acc
                                     state))
       ((unless (look-up-type-tuple-to-thm-alist root-type types-hd thms
                                                 term path-cond state))
        acc)
       (type-term `(,types-hd ,term))
       ((if (path-test acc type-term state))
        (super/subtype-to-judgements root-type types-tl term thms path-cond acc
                                     state)))
    (super/subtype-to-judgements root-type types-tl term thms path-cond
                                 `(if ,type-term ,acc 'nil) state)))
)

(define super/subtype-judgement-single ((type-judgement pseudo-termp)
                                        (path-cond pseudo-termp)
                                        (type-alst type-to-types-alist-p)
                                        (thms type-tuple-to-thm-alist-p)
                                        (acc pseudo-termp)
                                        state)
  :guard (type-predicate-p type-judgement type-alst)
  :returns (judgements pseudo-termp)
  (b* ((type-judgement (pseudo-term-fix type-judgement))
       (type-alst (type-to-types-alist-fix type-alst))
       (acc (pseudo-term-fix acc))
       ((unless (mbt (type-predicate-p type-judgement type-alst))) acc)
       ((list root-type term) type-judgement)
       (clock (len type-alst))
       (super/subtypes
        (super/subtype root-type type-alst nil clock)))
    (super/subtype-to-judgements root-type super/subtypes term thms path-cond
                                 acc state)))

(define super/subtype-judgements-acc ((judge pseudo-termp)
                                      (path-cond pseudo-termp)
                                      (type-alst type-to-types-alist-p)
                                      (thms type-tuple-to-thm-alist-p)
                                      (acc pseudo-termp)
                                      state)
  :returns (judgements pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judge))
  :verify-guards nil
  (b* ((judge (pseudo-term-fix judge))
       (acc (pseudo-term-fix acc))
       ((if (type-predicate-p judge type-alst))
        (super/subtype-judgement-single judge path-cond type-alst thms acc state))
       ((unless (is-conjunct? judge)) acc)
       ((if (equal judge ''t)) acc)
       ((list* & cond then &) judge)
       (first-acc (super/subtype-judgements-acc cond path-cond type-alst thms
                                                acc state)))
    (super/subtype-judgements-acc then path-cond type-alst thms first-acc
                                  state)))

(verify-guards super/subtype-judgements-acc)

(define super/subtype-judgements-fn ((judge pseudo-termp)
                                     (path-cond pseudo-termp)
                                     (type-alst type-to-types-alist-p)
                                     (thms type-tuple-to-thm-alist-p)
                                     state)
  :returns (judgements pseudo-termp)
  (super/subtype-judgements-acc judge path-cond type-alst thms judge state))

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
                                    (type-options->supertype-thm ,options)
                                    ,state)
     (super/subtype-judgements-fn ,judgements ,path-cond
                                  (type-options->subtype ,options)
                                  (type-options->subtype-thm ,options)
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
