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
(include-book "compose")
(include-book "identityp")

(local (include-book "assoc"))
(local (include-book "extensionality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-values ((values set::setp) (x mapp))
  :parents (omaps)
  :returns (map mapp)
  :short "Restrict an omap to entries whose value is in a given set."
  :long
  (xdoc::topstring-p
   "Retains only the key-value pairs of @('x')
    whose associated value belongs to @('values').
    All other pairs are dropped.")
  (if (emptyp x)
      nil
    (mv-let (k v)
        (head x)
      (if (set::in v values)
          (update k v
                  (restrict-values values (tail x)))
        (restrict-values values (tail x)))))
  :verify-guards :after-returns

  ///

  (defcong mequiv equal (restrict-values keys map) 2
           :hints (("Goal" :in-theory (disable mequiv))))

  (defrule restrict-values-when-left-emptyp
      (implies (set::emptyp vs)
               (not (restrict-values vs x)))
    :enable (restrict-values set::emptyp)
    :rule-classes (:rewrite :type-prescription))

  (defrule restrict-values-when-right-emptyp
      (implies (emptyp x)
               (equal (restrict-values vs x) nil))
    :enable restrict-values
    :rule-classes (:rewrite :type-prescription))

  (defrule assoc-of-restrict-values
      (equal (assoc k (restrict-values vs x))
             (and (set::in (cdr (assoc k x)) vs)
                  (assoc k x)))
    :enable restrict-values)

  (defruled assoc-of-restrict-values-when-in-keys
      (implies (set::in (cdr (assoc k x)) vs)
               (equal (assoc k (restrict-values vs x))
                      (assoc k x)))
    :enable restrict-values)

  (defruledl compose-is-restrict-values-when-X-identityp-helper
      (implies (identityp x)
               (equal (assoc k (compose x y))
                      (assoc k (restrict-values (keys x) y))))
    :enable (assoc
             assoc-of-restrict
             in-of-keys-to-assoc
             assoc-when-identityp
             assoc-of-compose))

  (defruled compose-is-restrict-values-when-X-identityp
      (implies (identityp x)
               (equal (compose x y)
                      (restrict-values (keys x) y)))
    :enable (extensionality
             compose-is-restrict-values-when-X-identityp-helper)))

(in-theory (disable assoc-of-restrict-values))
