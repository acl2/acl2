; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "apply-term")
(include-book "pseudo-termfn-listp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define apply-terms-same-args ((fns pseudo-termfn-listp)
                               (args pseudo-term-listp))
  :returns (terms "A @(tsee pseudo-term-listp).")
  :verify-guards nil
  :parents (std/system/term-transformations)
  :short "Apply each function symbol or lambda expression of a list
          to the same list of pseudo-term arguments,
          obtaining a list of corresponding function applications."
  :long
  (xdoc::topstring-p
   "This utility lifts @(tsee apply-term)
    from a single function to a list of functions.")
  (if (endp fns)
      nil
    (cons (apply-term (car fns) args)
          (apply-terms-same-args (cdr fns) args))))
