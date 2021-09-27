; Standard System Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-not-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (arg pseudo-termp :hyp :guard))
  :parents (std/system/term-queries)
  :short "Check if a term is a call of @(tsee not)."
  :long
  (xdoc::topstring
   (xdoc::p
    "If it is, the first result is @('t')
     and the other result is the argument.
     Otherwise, all the results are @('nil')."))
  (case-match term
    (('not arg) (mv t arg))
    (& (mv nil nil)))
  ///

  (defret acl2-count-of-check-not-call
    (implies yes/no
             (< (acl2-count arg)
                (acl2-count term)))
    :rule-classes :linear))
