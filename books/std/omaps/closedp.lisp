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
  (set::subset (values x) (keys x))
  ///

  (defcong mequiv equal (closedp x) 1)

  (defrule identityp-implies-closedp
      (implies (identityp x)
               (closedp x))
    :enable values-is-keys-when-identityp
    :rule-classes :forward-chaining))
