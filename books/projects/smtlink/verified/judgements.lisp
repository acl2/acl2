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

(include-book "type-options")
(include-book "evaluator")

(define only-one-var-acc ((term-lst pseudo-term-listp)
                          (term pseudo-termp)
                          (count natp))
  :returns (ok booleanp)
  (b* ((term-lst (pseudo-term-list-fix term-lst))
       (count (nfix count))
       ((unless (consp term-lst)) (equal count 1))
       ((cons first rest) term-lst)
       ((if (equal first term))
        (only-one-var-acc rest term (1+ count)))
       ((if (acl2::variablep first)) nil)
       ((if (acl2::fquotep first))
        (only-one-var-acc rest term count)))
    nil))

(define only-one-var ((term-lst pseudo-term-listp)
                      (term pseudo-termp))
  :returns (ok booleanp)
  (only-one-var-acc term-lst term 0))

(define type-predicate-p ((judge pseudo-termp)
                          (supertype-alst type-to-types-alist-p))
  :returns (ok booleanp)
  (and (pseudo-termp judge)
       (equal (len judge) 2)
       (symbolp (car judge))
       (not (equal (car judge) 'quote))
       (is-type? (car judge) supertype-alst))
  ///
  (more-returns
   (ok (implies ok
                (and (consp judge)
                     (symbolp (car judge))
                     (pseudo-termp (cadr judge))))
       :name implies-of-type-predicate-p)))

(define type-predicate-of-term ((judge pseudo-termp)
                                (term pseudo-termp)
                                (supertype-alst type-to-types-alist-p))
  :returns (ok booleanp)
  (and (pseudo-termp judge)
       (equal (len judge) 2)
       (symbolp (car judge))
       (not (equal (car judge) 'quote))
       (is-type? (car judge) supertype-alst)
       (equal term (cadr judge)))
  ///
  (more-returns
   (ok (implies ok (and (pseudo-termp judge)
                        (consp judge)
                        (symbolp (car judge))
                        (not (equal (car judge) 'quote))))
       :name implies-of-type-predicate-of-term)))

(define single-var-fncall-of-term ((judge pseudo-termp)
                                   (term pseudo-termp))
  :returns (ok booleanp)
  (and (pseudo-termp judge)
       (consp judge)
       (symbolp (car judge))
       (not (equal (car judge) 'quote))
       (only-one-var (cdr judge) term))
  ///
  (more-returns
   (ok (implies ok (and (pseudo-termp judge)
                        (consp judge)
                        (symbolp (car judge))
                        (not (equal (car judge) 'quote))))
       :name implies-of-single-var-fncall-of-term)))

(define judgement-of-term ((judge pseudo-termp)
                           (term pseudo-termp)
                           (supertype-alst type-to-types-alist-p))
  :returns (ok booleanp)
  (or (and (pseudo-termp term) (equal judge term))
      (type-predicate-of-term judge term supertype-alst)
      (single-var-fncall-of-term judge term))
  ///
  (more-returns
   (ok (implies ok (pseudo-termp judge))
       :name pseudo-termp-of-judgement-of-term))

  (defthm equal-judgement-of-term
    (implies (pseudo-termp term)
             (judgement-of-term term term supertype-alst)))

  (defthm type-predicate-of-term-implies-judgement-of-term
    (implies (type-predicate-of-term judge term supertype-alst)
             (judgement-of-term judge term supertype-alst)))
  )

#|
(judgement-of-term '(rationalp r1)
                   'r1
                   '((integerp . rationalp)))

(judgement-of-term '(< r1 '0)
                   'r1
                   '((integerp . rationalp)))

(judgement-of-term '(< r1 r2)
                   'r1
                   '((integerp . rationalp)))
|#

(encapsulate ()
(local (defthm lemma
         (implies (equal (len term) 4)
                  (not (consp (cddddr term))))
         :hints(("Goal"
                 :in-theory (disable len)
                 :expand ((len term)
                          (len (cdr term))
                          (len (cdr (cdr term)))
                          (len (cdr (cdr (cdr term))))
                          (len (cdr (cdr (cdr (cdr term))))))))))

(define is-conjunct? ((term pseudo-termp))
  :returns (ok booleanp)
  (b* ((term (pseudo-term-fix term)))
    (implies (not (equal term ''t))
             (and (consp term)
                  (equal (car term) 'if)
                  (equal (len term) 4)
                  (equal (cadddr term) ''nil))))
  ///
  (more-returns
   (ok (implies (and ok (pseudo-termp term) (not (equal term ''t)))
                (and (consp term)
                     (equal (len term) 4)
                     (pseudo-termp (cadr term))
                     (pseudo-termp (caddr term))))
       :name implies-of-is-conjunct?)
   (ok (implies ok (not (consp (cddddr term))))
       :name cddddr-when-is-conjunct?
       :hints (("Goal"
                :in-theory (e/d (pseudo-term-fix)))))
   (ok (implies (and ok (pseudo-termp term) (not (equal term ''t)))
                (< (acl2-count (caddr term))
                   (acl2-count term)))
       :name acl2-count-of-caddr-of-is-conjunct?
       :hints (("Goal"
                :in-theory (disable implies-of-is-conjunct?
                                    symbol-listp)))
       :rule-classes :linear)))
)

(defthm correctness-of-is-conjunct?
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp term)
                (is-conjunct? term)
                (not (equal term ''t))
                (alistp a)
                (ev-smtcp term a))
           (and (ev-smtcp (cadr term) a)
                (ev-smtcp (caddr term) a)))
  :hints (("Goal"
           :in-theory (enable is-conjunct?))))

(defthm consp-of-is-conjunct?
  (implies (and (pseudo-termp actuals-judgements)
                (not (equal actuals-judgements ''t))
                (is-conjunct? actuals-judgements))
           (and (consp (cdr actuals-judgements))
                (consp (cddr actuals-judgements))))
  :hints (("Goal"
           :in-theory (enable is-conjunct?))))

(defthm is-conjunct?-constructor
  (implies (and (pseudo-termp first)
                (pseudo-termp rest))
           (is-conjunct? `(if ,first ,rest 'nil)))
  :hints (("Goal"
           :in-theory (e/d (is-conjunct? pseudo-term-fix)
                           (implies-of-is-conjunct?
                            consp-of-is-conjunct?
                            symbol-listp
                            pseudo-term-listp-of-cdr-of-pseudo-termp)))))

(define is-conjunct-list? ((judges pseudo-termp)
                           (term pseudo-termp)
                           (supertype-alst type-to-types-alist-p))
  :returns (ok booleanp)
  :measure (acl2-count (pseudo-term-fix judges))
  :hints (("Goal"
           :in-theory (e/d (pseudo-term-fix)
                           (symbol-listp
                            pseudo-term-listp-of-symbol-listp
                            consp-of-is-conjunct?))))
  (b* ((term (pseudo-term-fix term))
       (judges (pseudo-term-fix judges))
       (supertype-alst (type-to-types-alist-fix supertype-alst))
       ((if (equal judges ''t)) t)
       ((if (judgement-of-term judges term supertype-alst)) t)
       ((unless (consp judges)) nil)
       ((list fn cond then nil-term) judges)
       ((unless (and (equal fn 'if) (equal nil-term ''nil))) nil))
    (and (is-conjunct-list? cond term supertype-alst)
         (is-conjunct-list? then term supertype-alst)))
  ///
  (more-returns
   (ok (implies (and ok (pseudo-termp judges) (pseudo-termp term)
                     (type-to-types-alist-p supertype-alst)
                     (not (equal judges ''t))
                     (not (judgement-of-term judges term supertype-alst)))
                (and (pseudo-termp (cadr judges))
                     (consp judges)
                     (consp (cdr judges))
                     (consp (cddr judges))))
       :name implies-of-is-conjunct-list?
       :hints (("Goal" :in-theory (enable pseudo-termp)))))

  (defthm t-of-is-conjunct-list?
    (is-conjunct-list? ''t term supertype-alst))
  (defthm term-of-is-conjunct-list?
    (implies (pseudo-termp term)
             (is-conjunct-list? term term supertype-alst)))
  (defthm judgement-of-term-is-conjunct-list?
    (implies (and (pseudo-termp judges)
                  (pseudo-termp term)
                  (type-to-types-alist-p supertype)
                  (judgement-of-term judges term supertype))
             (is-conjunct-list? judges term supertype)))
  )

(defthm construct-is-conjunct-list?
  (implies (and (pseudo-termp judges)
                (pseudo-termp term)
                (type-to-types-alist-p supertype)
                (is-conjunct-list? judges term supertype)
                (type-predicate-of-term judge term supertype))
           (is-conjunct-list? `(if ,judge ,judges 'nil) term supertype))
  :hints (("Goal"
           :in-theory (enable is-conjunct-list?))))

