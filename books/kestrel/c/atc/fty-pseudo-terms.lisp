; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "kestrel/fty/symbol-pseudoterm-alist" :dir :system)
(include-book "kestrel/std/system/check-and-call" :dir :system)
(include-book "kestrel/std/system/check-fn-call" :dir :system)
(include-book "kestrel/std/system/fsublis-var" :dir :system)
(include-book "kestrel/std/system/check-if-call" :dir :system)
(include-book "kestrel/std/system/check-lambda-call" :dir :system)
(include-book "kestrel/std/system/check-list-call" :dir :system)
(include-book "kestrel/std/system/check-mbt-call" :dir :system)
(include-book "kestrel/std/system/check-mbt-dollar-call" :dir :system)
(include-book "kestrel/std/system/check-mv-let-call" :dir :system)
(include-book "kestrel/std/system/check-not-call" :dir :system)
(include-book "kestrel/std/system/check-or-call" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ fty-pseudo-term-utilities
  :parents (atc-implementation)
  :short "FTY utilities for pseudo-terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "Many system utilities, e.g. built-in and in "
    (xdoc::seetopic "acl2::std/system" "Std/system")
    ", are written using the built-in ACL2 term API.
     When using these system utilities
     in code that uses the "
    (xdoc::seetopic "acl2::pseudo-term-fty" "FTY term API")
    ", there may be a slight ``mismatch'',
     e.g. in the way the two APIs fix non-terms,
     or in the fact that, for termination,
     the ACL2 API is based on @(tsee acl2-count)
     while the FTY API is based on @(tsee pseudo-term-count).")
   (xdoc::p
    "The mismatch can be bridged by introducing
     simple wrappers of those system utilities
     that fix the term (in the FTY way) and then call the utilities.
     Here we provide a number of such wrappers,
     which should be eventually moved to a more central place.")
   (xdoc::p
    "The wrappers are accompanied by theorems
     leveraged from the wrapped utilities.
     This way the wrappers can be left disabled in code that uses them.")
   (xdoc::p
    "The @(tsee acl2-count) vs. @(tsee pseudo-term-count) issue
     requires a bit more work.
     Suppose we have a utility that returns results
     that are @(tsee acl2-count)-smaller than its arguments
     (under suitable conditions).
     In order to prove that the wrapper returns results
     that are @(tsee pseudo-term-count)-smaller than its arguments,
     we cannot leverage the theorems about @(tsee acl2-count).
     Instead, we need to enable the utilities to prove the theorems,
     and we also need to enable some FTY pseudo-term operations,
     because we need to break the FTY pseudo-term abstraction:
     we use this approach to prove theorems
     about the original utilities and @(tsee pseudo-term-count)
     under @(tsee pseudo-termp) assumptions,
     from which then the desired theorems about the wrappers readily follow.
     The theorems about the original utilities and @(tsee pseudo-term-count)
     are useful to prove the analogous theorems of utilities that call them."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fty-check-fn-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (fn symbolp)
               (args pseudo-term-listp))
  :short "FTY version of @(tsee check-fn-call)."
  (check-fn-call (pseudo-term-fix term))
  ///

  (more-returns
   (args true-listp :rule-classes :type-prescription))

  (defret fty-check-fn-call-not-quote
    (not (equal fn 'quote)))

  (defrule pseudo-term-list-count-of-check-fn-call.args
    (implies (pseudo-termp term)
             (b* (((mv yes/no & args) (check-fn-call term)))
               (implies yes/no
                        (< (pseudo-term-list-count args)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable (check-fn-call
             pseudo-term-kind
             pseudo-term-call->args)
    :expand (pseudo-term-count term))

  (defret pseudo-term-list-count-of-fty-check-fn-call.args
    (implies yes/no
             (< (pseudo-term-list-count args)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fty-check-if-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (test pseudo-termp)
               (then pseudo-termp)
               (else pseudo-termp))
  :short "FTY version of @(tsee check-if-call)."
  (check-if-call (pseudo-term-fix term))
  ///

  (defrule pseudo-term-count-of-check-if-call.test
    (implies (pseudo-termp term)
             (b* (((mv yes/no test & &) (check-if-call term)))
               (implies yes/no
                        (< (pseudo-term-count test)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable (check-if-call
             pseudo-term-kind
             pseudo-term-call->args)
    :expand (pseudo-term-count term))

  (defret pseudo-term-count-of-fty-check-if-call.test
    (implies yes/no
             (< (pseudo-term-count test)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defrule pseudo-term-count-of-check-if-call.then
    (implies (pseudo-termp term)
             (b* (((mv yes/no & then &) (check-if-call term)))
               (implies yes/no
                        (< (pseudo-term-count then)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable (check-if-call
             pseudo-term-kind
             pseudo-term-call->args)
    :expand (pseudo-term-count term))

  (defret pseudo-term-count-of-fty-check-if-call.then
    (implies yes/no
             (< (pseudo-term-count then)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defrule pseudo-term-count-of-check-if-call.else
    (implies (pseudo-termp term)
             (b* (((mv yes/no & & else) (check-if-call term)))
               (implies yes/no
                        (< (pseudo-term-count else)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable (check-if-call
             pseudo-term-kind
             pseudo-term-call->args)
    :expand (pseudo-term-count term))

  (defret pseudo-term-count-of-fty-check-if-call.else
    (implies yes/no
             (< (pseudo-term-count else)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defrule pseudo-term-count-of-check-if-call
    (implies (pseudo-termp term)
             (b* (((mv yes/no test then else) (check-if-call term)))
               (implies yes/no
                        (< (+ (pseudo-term-count test)
                              (pseudo-term-count then)
                              (pseudo-term-count else))
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable (check-if-call
             pseudo-term-kind
             pseudo-term-call->args)
    :expand (pseudo-term-count term))

  (defret pseudo-term-count-of-fty-check-if-call
    (implies yes/no
             (< (+ (pseudo-term-count test)
                   (pseudo-term-count then)
                   (pseudo-term-count else))
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fty-check-lambda-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (formals symbol-listp)
               (body pseudo-termp)
               (args pseudo-term-listp))
  :short "FTY version of @(tsee check-lambda-call)."
  (check-lambda-call (pseudo-term-fix term))
  ///

  (defret len-of-fty-check-lambda-calls.formals-is-args
    (equal (len formals)
           (len args))
    :hints (("Goal"
             :expand ((pseudo-term-fix term))
             :in-theory (enable check-lambda-call))))

  (defret len-of-fty-check-lambda-calls.args-is-formals
    (equal (len args)
           (len formals))
    :hints (("Goal" :use len-of-fty-check-lambda-calls.formals-is-args)))

  (in-theory (disable len-of-fty-check-lambda-calls.formals-is-args
                      len-of-fty-check-lambda-calls.args-is-formals))

  (theory-invariant (incompatible
                     (:rewrite fty-len-of-check-lambda-calls.formals-is-args)
                     (:rewrite fty-len-of-check-lambda-calls.args-is-formals)))

  (more-returns
   (formals true-listp :rule-classes :type-prescription)
   (args true-listp :rule-classes :type-prescription))

  (defrule pseudo-term-count-of-check-lambda-call.body
    (implies (pseudo-termp term)
             (b* (((mv yes/no & body &) (check-lambda-call term)))
               (implies yes/no
                        (< (pseudo-term-count body)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable (check-lambda-call
             pseudo-term-kind
             pseudo-term-lambda->body)
    :expand (pseudo-term-count term))

  (defret pseudo-term-count-of-fty-check-lambda-call.body
    (implies yes/no
             (< (pseudo-term-count body)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defrule pseudo-term-list-count-of-check-lambda-call.args
    (implies (pseudo-termp term)
             (b* (((mv yes/no & & args) (check-lambda-call term)))
               (implies yes/no
                        (< (pseudo-term-list-count args)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable (check-lambda-call
             pseudo-term-kind
             pseudo-term-lambda->args)
    :expand (pseudo-term-count term))

  (defret pseudo-term-list-count-of-fty-check-lambda-call.args
    (implies yes/no
             (< (pseudo-term-list-count args)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defrule pseudo-term-count-of-check-lambda-call
    (implies (pseudo-termp term)
             (b* (((mv yes/no & body args) (check-lambda-call term)))
               (implies yes/no
                        (< (+ (pseudo-term-count body)
                              (pseudo-term-list-count args))
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable (check-lambda-call
             pseudo-term-count
             pseudo-term-list-count
             pseudo-term-kind
             pseudo-term-lambda->body
             pseudo-term-call->args))

  (defret pseudo-term-count-of-fty-check-lambda-call
    (implies yes/no
             (< (+ (pseudo-term-count body)
                   (pseudo-term-list-count args))
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fty-remove-equal-formals-actuals ((formals symbol-listp)
                                          (actuals pseudo-term-listp))
  :guard (= (len formals) (len actuals))
  :returns (mv (new-formals symbol-listp :hyp (symbol-listp formals))
               (new-actuals pseudo-term-listp))
  :short "FTY version of @(tsee remove-equal-formals-actuals)."
  (remove-equal-formals-actuals formals
                                (acl2::pseudo-term-list-fix actuals))
  ///

  (more-returns
   (new-formals true-listp :rule-classes :type-prescription)
   (new-actuals true-listp :rule-classes :type-prescription))

  (defret len-of-fty-remove-equal-formals-actuals.new-formals-is-new-actuals
    (equal (len new-formals)
           (len new-actuals))
    :hints
    (("Goal" :in-theory (enable remove-equal-formals-actuals
                                acl2::remove-equal-formals-actuals-same-len))))

  (defret len-of-fty-remove-equal-formals-actuals.new-actuals-is-new-formals
    (equal (len new-actuals)
           (len new-formals))
    :hints
    (("Goal"
      :use len-of-fty-remove-equal-formals-actuals.new-formals-is-new-actuals)))

  (in-theory
   (disable len-of-fty-remove-equal-formals-actuals.new-formals-is-new-actuals
            len-of-fty-remove-equal-formals-actuals.new-actuals-is-new-formals))

  (theory-invariant
   (incompatible
    (:rewrite
     len-of-fty-remove-equal-formals-actuals.new-formals-is-new-actuals)
    (:rewrite
     len-of-fty-remove-equal-formals-actuals.new-actuals-is-new-formals)))

  (defrule pseudo-term-list-count-of-remove-equal-formals-actuals
    (b* (((mv & new-actuals) (remove-equal-formals-actuals formals actuals)))
      (implies (pseudo-term-listp actuals)
               (<= (pseudo-term-list-count new-actuals)
                   (pseudo-term-list-count actuals))))
    :rule-classes :linear
    :enable (remove-equal-formals-actuals
             pseudo-term-list-count))

  (defret pseudo-term-list-count-of-fty-remove-equal-formals-actuals
    (<= (pseudo-term-list-count new-actuals)
        (pseudo-term-list-count actuals))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fty-check-not-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (arg pseudo-termp))
  :short "FTY version of @(tsee check-not-call)."
  (check-not-call (pseudo-term-fix term))
  ///

  (defrule pseudo-term-count-of-check-not-call.arg
    (implies (pseudo-termp term)
             (b* (((mv yes/no arg) (check-not-call term)))
               (implies yes/no
                        (< (pseudo-term-count arg)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable (check-not-call
             pseudo-term-kind
             pseudo-term-call->args)
    :expand (pseudo-term-count term))

  (defret pseudo-term-count-of-fty-check-not-call.arg
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fty-check-and-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (left pseudo-termp)
               (right pseudo-termp))
  :short "FTY version of @(tsee check-and-call)."
  (check-and-call (pseudo-term-fix term))
  ///

  (defrule pseudo-term-count-of-check-and-call.left
    (implies (pseudo-termp term)
             (b* (((mv yes/no left &) (check-and-call term)))
               (implies yes/no
                        (< (pseudo-term-count left)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable check-and-call)

  (defrule pseudo-term-count-of-check-and-call.right
    (implies (pseudo-termp term)
             (b* (((mv yes/no & right) (check-and-call term)))
               (implies yes/no
                        (< (pseudo-term-count right)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable check-and-call)

  (defret pseudo-term-count-of-fty-check-and-call.left
    (implies yes/no
             (< (pseudo-term-count left)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-fty-check-and-call.right
    (implies yes/no
             (< (pseudo-term-count right)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fty-check-or-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (left pseudo-termp)
               (right pseudo-termp))
  :short "FTY version of @(tsee check-or-call)."
  (check-or-call (pseudo-term-fix term))
  ///

  (defrule pseudo-term-count-of-check-or-call.left
    (implies (pseudo-termp term)
             (b* (((mv yes/no left &) (check-or-call term)))
               (implies yes/no
                        (< (pseudo-term-count left)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable check-or-call)

  (defrule pseudo-term-count-of-check-or-call.right
    (implies (pseudo-termp term)
             (b* (((mv yes/no & right) (check-or-call term)))
               (implies yes/no
                        (< (pseudo-term-count right)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable check-or-call)

  (defret pseudo-term-count-of-fty-check-or-call.left
    (implies yes/no
             (< (pseudo-term-count left)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-fty-check-or-call.right
    (implies yes/no
             (< (pseudo-term-count right)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fty-check-mv-let-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (mv-var symbolp)
               (vars symbol-listp)
               (indices nat-listp)
               (hides boolean-listp)
               (mv-term pseudo-termp)
               (body-term pseudo-termp))
  :short "FTY version of @(tsee check-mv-let-call)."
  (check-mv-let-call (pseudo-term-fix term))
  ///

  (defret len-of-fty-check-mv-let-call.indices/vars
    (implies yes/no
             (equal (len indices)
                    (len vars)))
    :hyp :guard
    :hints (("Goal"
             :in-theory (enable acl2::len-of-check-mv-let-call.indices/vars))))

  (defret len-of-fty-check-mv-let-call.hides/vars
    (implies yes/no
             (equal (len hides)
                    (len vars)))
    :hyp :guard
    :hints (("Goal"
             :in-theory (enable acl2::len-of-check-mv-let-call.hides/vars))))

  (in-theory (disable len-of-fty-check-mv-let-call.indices/vars
                      len-of-fty-check-mv-let-call.indices/vars))

  (defrule pseudo-term-count-of-check-mv-let-call.mv-term
    (implies (pseudo-termp term)
             (b* (((mv yes/no & & & & mv-term &) (check-mv-let-call term)))
               (implies yes/no
                        (< (pseudo-term-count mv-term)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable (check-mv-let-call
             pseudo-term-kind)
    :prep-lemmas
    ((defrule lemma
       (implies (and (pseudo-termp term)
                     (not (pseudo-term-case term :quote)))
                (<= (pseudo-term-list-count (cdr term))
                    (pseudo-term-count term)))
       :rule-classes :linear
       :expand (pseudo-term-count term)
       :enable (pseudo-term-call->args
                pseudo-term-kind))))

  (defret pseudo-term-count-of-fty-check-mv-let-call.mv-term
    (implies yes/no
             (< (pseudo-term-count mv-term)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defrule pseudo-term-count-of-check-mv-let-call.body-term
    (implies (pseudo-termp term)
             (b* (((mv yes/no & & & & & body-term) (check-mv-let-call term)))
               (implies yes/no
                        (< (pseudo-term-count body-term)
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable check-mv-let-call
    :prep-lemmas
    ((defrule lemma
       (implies (and (pseudo-termp term)
                     (consp (car term)))
                (< (pseudo-term-count (caddr (car term)))
                   (pseudo-term-count term)))
       :rule-classes :linear
       :expand (pseudo-term-count term)
       :enable (pseudo-term-lambda->body
                pseudo-term-kind))))

  (defret pseudo-term-count-of-fty-check-mv-let-call.body-term
    (implies yes/no
             (< (pseudo-term-count body-term)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defrule pseudo-term-count-of-check-mv-let-call
    (implies (pseudo-termp term)
             (b* (((mv yes/no & & & & mv-term body-term)
                   (check-mv-let-call term)))
               (implies yes/no
                        (< (+ (pseudo-term-count mv-term)
                              (pseudo-term-count body-term))
                           (pseudo-term-count term)))))
    :rule-classes :linear
    :enable (check-mv-let-call
             pseudo-term-kind
             pseudo-term-lambda->body
             pseudo-term-call->args
             pseudo-term-count
             pseudo-term-list-count))

  (defret pseudo-term-count-if-fty-check-mv-let-call
    (implies yes/no
             (b* (((mv yes/no & & & & mv-term body-term)
                   (fty-check-mv-let-call term)))
               (implies yes/no
                        (< (+ (pseudo-term-count mv-term)
                              (pseudo-term-count body-term))
                           (pseudo-term-count term)))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fty-check-list-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (elements pseudo-term-listp))
  :short "FTY version of @(tsee check-list-call)."
  (check-list-call (pseudo-term-fix term))
  ///

  (more-returns
   (elements true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fty-fsublis-var ((subst symbol-pseudoterm-alistp) (term pseudo-termp))
  :returns (new-term pseudo-termp)
  :short "FTY version of @(tsee fsublis-var)."
  (fsublis-var (acl2::symbol-pseudoterm-alist-fix subst)
               (pseudo-term-fix term))
  :prepwork
  ((defrulel lemma
     (implies (and (symbol-pseudoterm-alistp alist)
                   (pseudo-termp term))
              (pseudo-termp (fsublis-var alist term)))
     :enable acl2::symbol-pseudoterm-alistp-alt-def)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fty-fsublis-var-lst ((subst symbol-pseudoterm-alistp)
                             (terms pseudo-term-listp))
  :returns (new-terms pseudo-term-listp)
  :short "FTY version of @(tsee fsublis-var-lst)."
  (fsublis-var-lst (acl2::symbol-pseudoterm-alist-fix subst)
                   (pseudo-term-list-fix terms))

  :prepwork
  ((defrulel lemma
     (implies (and (symbol-pseudoterm-alistp subst)
                   (pseudo-term-listp terms))
              (pseudo-term-listp (fsublis-var-lst subst terms)))
     :enable acl2::symbol-pseudoterm-alistp-alt-def)))
