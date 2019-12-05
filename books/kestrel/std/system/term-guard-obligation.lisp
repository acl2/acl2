; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define term-guard-obligation ((term pseudo-termp) state)
  :returns (obligation "A @(tsee pseudo-termp).")
  :mode :program
  :parents (std/system/term-queries)
  :short "Formula expressing the guard obligation of a term."
  :long
  (xdoc::topstring-p
   "The case in which @('term') is a symbol is dealt with separately
    because @(tsee guard-obligation)
    interprets a symbol as a function or theorem name, not as a variable.")
  (b* (((when (symbolp term)) *t*)
       ((mv erp val) (guard-obligation term nil nil t __function__ state))
       ((when erp)
        (raise "Error ~x0 when computing the guard obligation of ~x1."
               erp term))
       (obligation-clauses (cadr val))
       (obligation-formula (termify-clause-set obligation-clauses)))
    obligation-formula))
