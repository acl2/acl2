; Ordered Maps (Omaps) Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "core")
(include-book "identityp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define closedp ((x mapp))
  :returns (yes/no booleanp)
  :short "Check if an omap is closed under its domain."
  :long
  (xdoc::topstring-p
   "An omap is closed if it is empty or
    its set of values is a subset of its set of keys.")
  (subset (values x) (keys x))
  ///

  (defcong mequiv equal (closedp x) 1)

  (defrule identityp-implies-closedp
      (implies (identityp x)
               (closedp x))
    :enable values-is-keys-when-identityp
    :rule-classes :forward-chaining))
