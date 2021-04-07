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
;; for symbol-fix
(include-book "centaur/fty/basetypes" :dir :system)
;; for symbol-list-fix
(include-book "centaur/fty/baselists" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)
;; To be compatible with Arithmetic books
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
;; Meta-extract stuff
(include-book "clause-processors/just-expand" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)

;; Include SMT books
(include-book "hint-interface")
(include-book "evaluator")

(local
(defthm alistp-of-pairlis$
  (alistp (acl2::pairlis$ a b)))
)

(encapsulate ()

  (local (defthm pseudo-term-substp-of-pairlis$-for-pseudo-lambda
           (implies (and (pseudo-term-listp x) (pseudo-lambdap y))
                    (acl2::pseudo-term-substp (pairlis$ (lambda-formals y) x)))))

  (define lambda-substitution ((fn-call pseudo-lambdap)
                               (fn-actuals pseudo-term-listp))
    :guard-hints (("Goal"
                   :in-theory (e/d () (alistp-of-pairlis$
                                       acl2::true-listp-when-symbol-listp))
                   :use ((:instance acl2::true-listp-when-symbol-listp
                                    (acl2::x (cadr fn-call)))
                         (:instance alistp-of-pairlis$
                                    (a (cadr fn-call))
                                    (b fn-actuals)))))
    :returns (subst-term
              pseudo-termp
              :hints (("Goal"
                       :in-theory (e/d ()
                                       (pseudo-term-substp-of-pairlis$-for-pseudo-lambda
                                        acl2::return-type-of-substitute-into-term.xx))
                       :use ((:instance
                              pseudo-term-substp-of-pairlis$-for-pseudo-lambda
                              (x fn-actuals)
                              (y fn-call))
                             (:instance
                              acl2::return-type-of-substitute-into-term.xx
                              (x (lambda-body (pseudo-lambda-fix fn-call)))
                              (al (pairlis$ (lambda-formals
                                             (pseudo-lambda-fix fn-call))
                                            (pseudo-term-list-fix fn-actuals))))))))
    (b* ((fn-call (pseudo-lambda-fix fn-call))
         (fn-actuals (pseudo-term-list-fix fn-actuals))
         (formals (lambda-formals fn-call))
         (body (lambda-body fn-call)))
      (acl2::substitute-into-term body (pairlis$ formals fn-actuals)))))

(local (defthm lambda-alist-of-pairlis$
         (equal (ev-smtcp-alist (pairlis$ x y) a)
                (pairlis$ x (ev-smtcp-lst y a)))))

(defthm lambda-substitution-correct
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (alistp a)
                (pseudo-lambdap fn-call)
                (pseudo-term-listp fn-actuals))
           (equal
            (ev-smtcp (lambda-substitution fn-call fn-actuals) a)
            (ev-smtcp (cons fn-call fn-actuals) a)))
  :hints (("Goal"
           :in-theory (enable lambda-substitution))))
