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

(include-book "judgements")
(include-book "partial-eval")
(include-book "term-substitution")

(set-state-ok t)

(local (in-theory (disable symbol-listp pseudo-termp-opener)))

;; -------------------------------------------------------------------
;;        Functions about path-cond

(define path-test ((path-cond pseudo-termp)
                   (expr pseudo-termp)
                   state)
  :returns (ok booleanp)
  (b* ((path-cond (pseudo-term-fix path-cond))
       (expr (pseudo-term-fix expr))
       (substed-cond (term-substitution path-cond `((,expr . 'nil)) t))
       ((mv err eval-cond) (partial-eval substed-cond nil state))
       ((if err) nil)
       ((unless eval-cond) t))
    nil))

(define path-test-list ((path-cond pseudo-termp)
                        (expr-conj pseudo-termp)
                        state)
  :returns (ok booleanp)
  :measure (acl2-count (pseudo-term-fix expr-conj))
  (b* ((path-cond (pseudo-term-fix path-cond))
       (expr-conj (pseudo-term-fix expr-conj))
       ((unless (is-conjunct? expr-conj))
        (path-test path-cond expr-conj state))
       ((if (equal expr-conj ''t)) t)
       ((list & expr-hd expr-tl &) expr-conj)
       (yes? (path-test path-cond expr-hd state))
       ((if yes?) (path-test-list path-cond expr-tl state)))
    nil))

#|
(path-test-list '(if (integerp x) (if (null x) 't 'nil) 'nil)
                '(if (integerp x) 't 'nil)
                state)
(path-test-list '(if (integerp x) (if (null x) 't 'nil) 'nil)
                '(if (rationalp x) 't 'nil)
                state)
(path-test-list '(if (integerp x) (if (null x) 't 'nil) 'nil)
                '(if x 't 'nil)
                state)
(path-test-list '(if (if (integerp x)
                         (if (null x) 't 'nil) 'nil)
                     (rationalp x)
                   'nil)
                '(if x (if (integerp x) 't 'nil) 'nil)
                state)
(path-test-list '(IF (IF (RATIONALP R1) 'T 'NIL)
                     (IF (IF (RATIONAL-INTEGER-ALISTP AL)
                             'T
                             'NIL)
                         'T
                         'NIL)
                     'NIL)
                '(rational-integer-alistp al)
                state)
|#

(define path-test-list-or ((path-cond pseudo-termp)
                           (expr-conj pseudo-termp)
                           state)
  :returns (ok booleanp)
  :measure (acl2-count (pseudo-term-fix expr-conj))
  (b* ((path-cond (pseudo-term-fix path-cond))
       (expr-conj (pseudo-term-fix expr-conj))
       ((unless (is-conjunct? expr-conj))
        (path-test path-cond expr-conj state))
       ((if (equal expr-conj ''t)) nil)
       ((list & expr-hd expr-tl &) expr-conj)
       (yes? (path-test path-cond expr-hd state))
       ((if yes?) t))
    (path-test-list-or path-cond expr-tl state)))

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

(define look-up-path-cond ((term pseudo-termp)
                           (path-cond pseudo-termp)
                           (supertype-alst type-to-types-alist-p))
  :returns (type-term pseudo-termp)
  (look-up-path-cond-acc term path-cond supertype-alst ''t))

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

(define shadow-path-cond ((formals symbol-listp)
                          (path-cond pseudo-termp))
  :returns (shadowed-path-cond pseudo-termp)
  (shadow-path-cond-acc formals path-cond ''t))

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
