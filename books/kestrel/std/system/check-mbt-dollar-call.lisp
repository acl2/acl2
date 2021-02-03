; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/basic/mbt-dollar" :dir :system)
(include-book "std/util/define" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-mbt$-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp) (arg pseudo-termp :hyp :guard))
  :parents (std/system/term-queries)
  :short "Check if a term is a call of @(tsee mbt$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "If it is, return its argument.
     If it is not, all results are @('nil').")
   (xdoc::p
    "In translated terms, @('(mbt$ x)') is
     @('(return-last \'mbe1-raw \'t x)')."))
  (case-match term
    (('return-last ''mbe1-raw ''t ('if x ''t ''nil)) (mv t x))
    (& (mv nil nil)))
  ///

  (defret acl2-count-of-check-mbt$-call.arg
    (implies yes/no
             (< (acl2-count arg) (acl2-count term)))
    :rule-classes :linear))
