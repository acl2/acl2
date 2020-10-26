;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 9th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
;; Meta-extract stuff
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/sublis-var-meaning" :dir :system)

(include-book "hint-please")
(include-book "hint-interface")
(include-book "computed-hints")
(include-book "lambda-substitution")
(include-book "evaluator")

(include-book "ordinals/lexicographic-ordering" :dir :system)
(set-state-ok t)

(define type-thm-remove-lambda ((func smt-function-p)
                                state)
  :returns (type-thm pseudo-termp) ;; type-fix
  (b* ((func (smt-function-fix func))
       (returns (smt-function->returns func))
       ((unless (and (car returns) (null (cdr returns))))
        (er hard? 'return-type=>type-thm-remove-lambda "Smtlink requires
                                exactly one returns~%" returns))
       (type (decl->type (car returns)))
       (type-of-f (hint-pair->name type))
       (type-thm (acl2::meta-extract-formula-w type-of-f (w state)))
       ((unless (and (pseudo-termp type-thm)
                     (consp type-thm)
                     (pseudo-lambdap (car type-thm))
                     (pseudo-term-listp (cdr type-thm))))
        (er hard? 'return-type=>type-thm-remove-lambda "Type theorem type-of-f is
 not of the expected shape: ~q0" type-thm))
       ((cons fn fn-actuals) type-thm)
       (type-thm-w/o-lambda (lambda-substitution fn fn-actuals)))
    type-thm-w/o-lambda))


;; BOZO: Should be able to do functional-instantiation of
;; lambda-substitution-correct, but I got lost at the symbols from package acl2
;; and current package
(local (defthm ev-smtcp-alist-of-pairlis$
         (equal (ev-smtcp-alist (pairlis$ x y) a)
                (pairlis$ x (ev-smtcp-lst y a)))))

(defthm lambda-substitution-correct-uninterpreted
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (alistp a)
                (pseudo-lambdap fn-call)
                (pseudo-term-listp fn-actuals))
           (equal
            (ev-smtcp (lambda-substitution fn-call fn-actuals) a)
            (ev-smtcp (cons fn-call fn-actuals) a)))
  :hints (("Goal"
           :in-theory (enable lambda-substitution))))

(defthm type-thm-remove-lambda-correct
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (alistp a))
           (or (null (type-thm-remove-lambda func state))
               (ev-smtcp (type-thm-remove-lambda func state) a)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (type-thm-remove-lambda
                            ev-smtcp-of-fncall-args)
                           (pseudo-term-listp
                            pseudo-termp
                            car-cdr-elim
                            w
                            lambda-substitution-correct-uninterpreted))
           :use ((:instance
                  lambda-substitution-correct-uninterpreted
                  (a a)
                  (fn-call
                   (car (meta-extract-formula (hint-pair->name (decl->type (car (smt-function->returns func))))
                                              state)))
                  (fn-actuals
                   (cdr (meta-extract-formula (hint-pair->name (decl->type (car (smt-function->returns func))))
                                              state)))
                  ))
           )))

(define return-type-substitution ((term pseudo-termp)
                                  (type-thm pseudo-termp))
  :returns (new-term pseudo-termp
                     :hints (("Goal"
                              :in-theory (enable pseudo-termp
                                                 pseudo-term-fix
                                                 pairlis$))))
  (b* ((term (pseudo-term-fix term))
       (type-thm (pseudo-term-fix type-thm))
       (vars (reverse (acl2::simple-term-vars type-thm)))
       ((unless (and (consp term)
                     (acl2::pseudo-term-substp (pairlis$ vars (cdr term)))))
        (prog2$ (er hard? 'return-type=>return-type-substitution
                    "acl2::simple-term-vars failed with ~p0
                                    and ~p1" type-thm term)
                nil)))
    (acl2::substitute-into-term type-thm (pairlis$ vars (cdr term)))))

(define type-thm-full ((term pseudo-termp)
                       (func smt-function-p)
                       state)
  :returns (new-term pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (type-thm-w/o-lambda (type-thm-remove-lambda func state))
       ((unless type-thm-w/o-lambda)
        (prog2$ (er hard? 'return-type=>type-thm-full
                    "Something is wrong with type-thm-remove-lambda.")
                nil))
       (type-thm (return-type-substitution term type-thm-w/o-lambda))
       ((unless type-thm)
        (prog2$ (er hard? 'return-type=>type-thm-full
                    "Something is wrong with return-type-substitution.")
                nil)))
    type-thm))

(local (defthm alistp-of-unev-alist (alistp (ev-smtcp-alist x a))))

(defthm type-thm-full-correct
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (alistp a)
                (pseudo-termp term))
           (or (null (type-thm-full term func state))
               (ev-smtcp (type-thm-full term func state) a)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (type-thm-full
                            return-type-substitution)
                           (type-thm-remove-lambda-correct))
           :use ((:instance type-thm-remove-lambda-correct
                            (func func)
                            (a (pairlis$
                                (reverse (acl2::simple-term-vars
                                          (type-thm-remove-lambda func state)))
                                (ev-smtcp-lst (cdr term) a)))))
           )))
