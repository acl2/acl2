; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-if-call")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-or-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (left pseudo-termp :hyp :guard)
               (right pseudo-termp :hyp :guard))
  :parents (std/system/term-queries)
  :short "Check if a term is a (translated) call of @(tsee or)."
  :long
  (xdoc::topstring
   "If it is, return its disjuncts.
    If it is not, all results are @('nil').")
  (b* (((mv ifp test then else) (check-if-call term))
       ((when (not ifp)) (mv nil nil nil)))
    (if (equal test then)
        (mv t test else)
      (mv nil nil nil)))
  ///

  (defret acl2-count-of-check-or-call.left
    (implies yes/no
             (< (acl2-count left)
                (acl2-count term)))
    :rule-classes :linear)

  (defret acl2-count-of-check-or-call.right
    (implies yes/no
             (< (acl2-count right)
                (acl2-count term)))
    :rule-classes :linear))
