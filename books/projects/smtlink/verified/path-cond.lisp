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

(include-book "basics")
(include-book "judgements")
(include-book "term-substitution")

;; -------------------------------------------------------------------
;;        Functions about path-cond

;; look-up-path-cond will ignore the whole branch of or's and only look for top
;; level and's
(define look-up-path-cond-acc ((term pseudo-termp)
                               (path-cond pseudo-termp)
                               (supertype-alst type-to-types-alist-p)
                               (acc pseudo-termp))
  :returns (type-term pseudo-termp)
  :measure (acl2-count (pseudo-term-fix path-cond))
  :verify-guards nil
  (b* ((term (pseudo-term-fix term))
       (path-cond (pseudo-term-fix path-cond))
       (acc (pseudo-term-fix acc))
       ((if (equal path-cond ''t)) acc)
       ((if (judgement-of-term path-cond term supertype-alst))
        `(if ,path-cond ,acc 'nil))
       ((unless (is-conjunct? path-cond)) acc)
       ((list* & path-hd path-tl &) path-cond)
       (new-acc (look-up-path-cond-acc term path-hd supertype-alst acc)))
    (look-up-path-cond-acc term path-tl supertype-alst new-acc)))

(verify-guards look-up-path-cond-acc)

(defthm correctness-of-lookup-path-cond-acc
   (implies (and (ev-smtcp-meta-extract-global-facts)
                 (pseudo-termp term)
                 (pseudo-termp path-cond)
                 (pseudo-termp acc)
                 (type-to-types-alist-p supertype-alst)
                 (alistp a)
                 (ev-smtcp path-cond a)
                 (ev-smtcp acc a))
            (ev-smtcp (look-up-path-cond-acc term path-cond supertype-alst acc)
                      a))
   :hints (("Goal"
            :in-theory (e/d (look-up-path-cond-acc is-conjunct?)
                            (implies-of-is-conjunct?
                             member-equal symbol-listp
                             consp-of-is-conjunct?
                             pseudo-term-listp-of-symbol-listp
                             default-cdr)))))

(define look-up-path-cond ((term pseudo-termp)
                           (path-cond pseudo-termp)
                           (supertype-alst type-to-types-alist-p))
  :returns (type-term pseudo-termp)
  (look-up-path-cond-acc term path-cond supertype-alst ''t)
  ///
  (defthm correctness-of-lookup-path-cond
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp term)
                  (pseudo-termp path-cond)
                  (type-to-types-alist-p supertype-alst)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (look-up-path-cond term path-cond supertype-alst)
                       a))
    :hints (("Goal"
             :expand (look-up-path-cond term path-cond supertype-alst)))))

#|
(look-up-path-cond 'r1
                   '(if (if (rational-integer-alistp al)
                            (if (rationalp r1)
                                (assoc-equal r1 al)
                              'nil)
                          'nil)
                        't
                      'nil)
                   '((integerp . (rationalp))
                     (rationalp)
                     (rational-integer-alistp)))

(look-up-path-cond 'r1
                   '(if (if (< r1 '0)
                            (if (rationalp r1)
                                (assoc-equal r1 al)
                              'nil)
                          'nil)
                        't
                      'nil)
                   '((integerp . rationalp)
                     (rationalp)))

(look-up-path-cond 'x
                   '(if (if x
                            (if (maybe-integerp x)
                                't
                              'nil)
                          'nil)
                        't
                      'nil)
                   '((integerp . rationalp)
                     (rationalp)
                     (maybe-integerp)))

(look-up-path-cond 'x
                   '(if (if (not x)
                            (if (maybe-integerp x)
                                't
                              'nil)
                          'nil)
                        't
                      'nil)
                   '((integerp . rationalp)
                     (rationalp)
                     (maybe-integerp)))

(look-up-path-cond 'x
                   '(if (not x)
                        (if x 't (if (maybe-integerp x) 't 'nil))
                      'nil)
                   '((integerp . rationalp)
                     (rationalp)
                     (maybe-integerp)))
|#

(define path-test ((path-cond pseudo-termp)
                   (expr pseudo-termp))
  :returns (ok booleanp)
  :measure (acl2-count (pseudo-term-fix path-cond))
  (b* ((expr (pseudo-term-fix expr))
       (path-cond (pseudo-term-fix path-cond))
       ((if (equal path-cond ''t)) nil)
       ((if (equal path-cond expr)) t)
       ((unless (is-conjunct? path-cond)) nil)
       ((list* & path-hd path-tl &) path-cond))
    (or (path-test path-hd expr)
        (path-test path-tl expr)))
  ///
  (defthm correctness-of-path-test
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (pseudo-termp expr)
                  (pseudo-termp path-cond)
                  (alistp a)
                  (ev-smtcp path-cond a)
                  (path-test path-cond expr))
             (ev-smtcp expr a))
    :hints (("Goal"
             :in-theory (e/d (path-test is-conjunct?)
                             (implies-of-is-conjunct?
                              consp-of-is-conjunct?
                              symbol-listp
                              pseudo-term-listp-of-symbol-listp
                              acl2::symbol-listp-of-cdr-when-symbol-listp
                              default-car default-cdr))))))

(define path-test-list ((path-cond pseudo-termp)
                        (expr-conj pseudo-termp))
  :returns (ok booleanp)
  :measure (acl2-count (pseudo-term-fix expr-conj))
  (b* ((path-cond (pseudo-term-fix path-cond))
       (expr-conj (pseudo-term-fix expr-conj))
       ((unless (is-conjunct? expr-conj))
        (path-test path-cond expr-conj))
       ((if (equal expr-conj ''t)) t)
       ((list & expr-hd expr-tl &) expr-conj)
       (yes? (path-test path-cond expr-hd))
       ((if yes?) (path-test-list path-cond expr-tl)))
    nil))

(defthm correctness-of-path-test-list
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-termp expr-conj)
                (pseudo-termp path-cond)
                (alistp a)
                (ev-smtcp path-cond a)
                (path-test-list path-cond expr-conj))
           (ev-smtcp expr-conj a))
  :hints (("Goal"
           :in-theory (e/d (path-test-list is-conjunct?)
                           (implies-of-is-conjunct?
                            consp-of-is-conjunct?
                            symbol-listp
                            pseudo-term-listp-of-symbol-listp
                            acl2::symbol-listp-of-cdr-when-symbol-listp
                            default-car default-cdr)))))

#|
(path-test-list '(if (integerp x) (if (null x) 't 'nil) 'nil)
                '(if (integerp x) 't 'nil))
(path-test-list '(if (integerp x) (if (null x) 't 'nil) 'nil)
                '(if (rationalp x) 't 'nil))
(path-test-list '(if (integerp x) (if (null x) 't 'nil) 'nil)
                '(if x 't 'nil))
(path-test-list '(if (if (integerp x)
                         (if (null x) 't 'nil) 'nil)
                     (rationalp x)
                   'nil)
                '(if x (if (integerp x) 't 'nil) 'nil))
(path-test-list '(IF (IF (RATIONALP R1) 'T 'NIL)
                     (IF (IF (RATIONAL-INTEGER-ALISTP AL)
                             'T
                             'NIL)
                         'T
                         'NIL)
                     'NIL)
                '(rational-integer-alistp al))
|#

(define path-test-list-or ((path-cond pseudo-termp)
                           (expr-conj pseudo-termp))
  :returns (ok booleanp)
  :measure (acl2-count (pseudo-term-fix expr-conj))
  (b* ((path-cond (pseudo-term-fix path-cond))
       (expr-conj (pseudo-term-fix expr-conj))
       ((unless (is-conjunct? expr-conj))
        (path-test path-cond expr-conj))
       ((if (equal expr-conj ''t)) nil)
       ((list & expr-hd expr-tl &) expr-conj)
       (yes? (path-test path-cond expr-hd))
       ((if yes?) t))
    (path-test-list-or path-cond expr-tl)))

;; shadow-path-cond-acc will shadow the whole or branch if it contains
;; variables shadowed by formals.
(define shadow-path-cond-acc ((formals symbol-listp)
                              (path-cond pseudo-termp)
                              (acc pseudo-termp))
  :returns (shadowed-path-cond pseudo-termp)
  :measure (acl2-count (pseudo-term-fix path-cond))
  :verify-guards nil
  (b* ((formals (symbol-list-fix formals))
       (path-cond (pseudo-term-fix path-cond))
       (acc (pseudo-term-fix acc))
       ((if (and (not (is-conjunct? path-cond))
                 (dumb-occur-vars-or formals path-cond)))
        acc)
       ((unless (is-conjunct? path-cond))
        `(if ,path-cond ,acc 'nil))
       ((if (equal path-cond ''t)) acc)
       ((list* & path-hd path-tl &) path-cond)
       (new-acc (shadow-path-cond-acc formals path-hd acc)))
    (shadow-path-cond-acc formals path-tl new-acc)))

(verify-guards shadow-path-cond-acc)

(defthm correctness-of-shadow-path-cond-acc
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (symbol-listp formals)
                (pseudo-termp path-cond)
                (pseudo-termp acc)
                (alistp a)
                (ev-smtcp path-cond a)
                (ev-smtcp acc a))
           (ev-smtcp (shadow-path-cond-acc formals path-cond acc) a))
  :hints (("Goal"
           :in-theory (e/d (shadow-path-cond-acc is-conjunct?)
                           (symbol-listp default-car default-cdr
                                         consp-of-is-conjunct?
                                         pseudo-term-listp-of-symbol-listp)))))

(define shadow-path-cond ((formals symbol-listp)
                          (path-cond pseudo-termp))
  :returns (shadowed-path-cond pseudo-termp)
  (shadow-path-cond-acc formals path-cond ''t)
  ///
  (defthm correctness-of-shadow-path-cond
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (symbol-listp formals)
                  (pseudo-termp path-cond)
                  (alistp a)
                  (ev-smtcp path-cond a))
             (ev-smtcp (shadow-path-cond formals path-cond) a))
    :hints (("Goal"
             :in-theory (enable shadow-path-cond))))
)

#|
(shadow-path-cond '(x)
                  '(if (not x) (if x 't (if (maybe-integerp x) 't nil))))

(shadow-path-cond '(x)
                  '(if (if (not x)
                           (if (maybe-integerp x)
                               't 'nil)
                         'nil)
                       't 'nil))

(shadow-path-cond '(x)
                  '(if (if (not x)
                           (if (maybe-integerp x)
                               't 'nil)
                         'nil)
                       (if (< '0 y)
                           (if (rationalp z) 't 'nil)
                         'nil)
                     'nil))
|#
