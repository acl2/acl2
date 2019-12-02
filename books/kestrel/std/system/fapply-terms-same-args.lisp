; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fapply-term")
(include-book "pseudo-termfn-listp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fapply-terms-same-args ((fns pseudo-termfn-listp)
                                (args pseudo-term-listp))
  :returns (terms "A @(tsee pseudo-term-listp).")
  :verify-guards nil
  :parents (std/system/term-transformations)
  :short "Variant of @(tsee apply-terms-same-args)
          that performs no simplification."
  :long
  (xdoc::topstring-p
   "The meaning of the starting @('f') in the name of this utility
    is analogous to @(tsee fcons-term) compared to @(tsee cons-term).")
  (if (endp fns)
      nil
    (cons (fapply-term (car fns) args)
          (fapply-terms-same-args (cdr fns) args))))
