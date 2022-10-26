; Standard System Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/typed-alists/symbol-pseudoterm-alistp" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define one-way-unify$ ((pat pseudo-termp) (term pseudo-termp) state)
  :returns (mv (okp booleanp)
               (subst symbol-pseudoterm-alistp))
  :parents (std/system/term-queries)
  :short "A logic-mode guard-verified version of @('one-way-unify')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The built in @('one-way-unify') matches a term to a pattern,
     returning a substituion of terms to variables if successful.
     The first result is a boolean indicating
     if the matching was successful or not;
     the second result is the substitution.")
   (xdoc::p
    "This @('one-way-unify$') function takes a state as additional argument,
     which it needs to call @(tsee magic-ev-fncall) on @('one-way-unify').
     It also ensures that the first result is a boolean and that,
     if the first result is @('t'), then the second one is a substitution,
     i.e. an alist from symbols (variables) to terms."))
  (b* (((mv erp okp+subst) (magic-ev-fncall 'one-way-unify
                                            (list pat term)
                                            state
                                            nil
                                            t))
       ((when erp)
        (raise "Internal error: ~@0" erp)
        (mv nil nil))
       ((unless (and (true-listp okp+subst)
                     (= (len okp+subst) 2)))
        (raise "Internal error: ONE-WAY-UNIFY returned ~x0." okp+subst)
        (mv nil nil))
       (okp (first okp+subst))
       (subst (second okp+subst))
       ((unless (booleanp okp))
        (raise "Internal error: ONE-WAY-UNIFY's first result is ~x0." okp)
        (mv nil nil))
       ((unless (symbol-pseudoterm-alistp subst))
        (raise "Internal error: ONE-WAY-UNIFY's second result is ~x0." subst)
        (mv nil nil)))
    (mv okp subst)))
