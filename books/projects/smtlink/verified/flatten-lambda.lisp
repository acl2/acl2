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

(include-book "term-substitution")
(include-book "../utils/pseudo-term")

;; ---------------------------------------
;;         smt-flatten-lambda

(define smt$flatten-lambda$ ((select booleanp)
                             (term t))
  (declare (ignore select))
  term)

(defthm smt$flatten-lambda$-forward
  (implies (smt$flatten-lambda$ select term)
           term)
  :rule-classes :forward-chaining)

(in-theory (disable (:d smt$flatten-lambda$)
                    (:e smt$flatten-lambda$)
                    (:t smt$flatten-lambda$)))

;; --------------------------------------

(define is-smt$flatten-lambda$ ((x pseudo-termp))
  :returns (ok booleanp)
  (b* ((x (pseudo-term-fix x)))
    (and (consp x)
         (equal (len x) 3)
         (equal (car x) 'smt$flatten-lambda$)
         (consp (cadr x))
         (acl2::fquotep (cadr x))
         (booleanp (cadr (cadr x))))))

(local (in-theory (enable is-smt$flatten-lambda$)))

(defines flatten-lambda
  :well-founded-relation l<
  :verify-guards nil

  (define flatten-lambda ((term pseudo-termp)
                          (flatten? booleanp)
                          (clock natp))
    :returns (new-term pseudo-termp)
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-fix term)))
    (b* ((term (pseudo-term-fix term))
         (clock (nfix clock))
         ((if (zp clock))
          (er hard? 'flatten-lambda=>flatten-lambda
              "Run out of clock.~%"))
         ((if (or (acl2::variablep term)
                  (acl2::fquotep term)))
          term)
         ((if (is-smt$flatten-lambda$ term))
          (flatten-lambda (caddr term) (cadr (cadr term)) clock))
         ((cons fn actuals) term)
         (flattened-actuals
          (flatten-lambda-list actuals flatten? clock))
         ((unless (mbt (equal (len actuals) (len flattened-actuals)))) nil)
         ((if (or (symbolp fn) (null flatten?)))
          `(,fn ,@flattened-actuals))
         ((unless (mbt (and (pseudo-lambdap fn) flatten?))) nil)
         (body (lambda-body fn))
         (formals (lambda-formals fn))
         (new-term (term-substitution body (pairlis$ formals actuals) nil)))
      (flatten-lambda new-term flatten? (1- clock))))

  (define flatten-lambda-list ((term-lst pseudo-term-listp)
                               (flatten? booleanp)
                               (clock natp))
    :returns (new-term pseudo-term-listp)
    :measure (list (nfix clock)
                   (acl2-count (pseudo-term-list-fix term-lst)))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         ((unless (consp term-lst)) nil)
         ((cons term-hd term-tl) term-lst))
      (cons (flatten-lambda term-hd flatten? clock)
            (flatten-lambda-list term-tl flatten? clock))))
  )

(defthm flatten-lambda-list-maintain-length
  (implies (and (pseudo-term-listp term-lst))
           (equal (len (flatten-lambda-list term-lst flatten? clock))
                  (len term-lst)))
  :hints (("Goal"
           :in-theory (enable flatten-lambda flatten-lambda-list)
           :expand (flatten-lambda-list term-lst flatten? clock))))

(verify-guards flatten-lambda
  :hints (("Goal" :in-theory (disable len))))

(define flatten-lambda-top ((term pseudo-termp)
                            (flatten? booleanp))
  :returns (new-term pseudo-termp)
  (flatten-lambda term flatten? (acl2-count term)))

#|
(flatten-lambda-top
 '((lambda (x)
     (+ x (smt$flatten-lambda$
           'nil
           ((lambda (y) (+ x y)) '2))))
   '1)
 t)

(flatten-lambda-top
 '(if (if (rational-integer-alistp al)
          (if (rationalp r1)
              (assoc-equal r1 al)
            'nil)
        'nil)
      ((lambda (x y)
         (< (binary-+ (cdr (assoc-equal y x))
                      (unary-- (cdr (assoc-equal y x))))
            '2))
       al r1)
    't)
 t)
|#
