; Ordered Maps (Omaps) Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)
; Contributing Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "core")
(include-book "compose")
(include-book "identityp")
(include-book "injectivep")

(local (include-book "extensionality"))
(local (include-book "update"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define inverse ((x mapp))
  :parents (omaps)
  :returns (map mapp)
  :short "Compute the inverse of an omap."
  :long
  (xdoc::topstring-p
   "Maps each value @('v') of @('x') back to its corresponding key @('k').
    The result is well-behaved when @('x') is injective;
    see @(tsee injectivep). For non-injective maps,
    each value is mapped to the smallest corresponding key "
   (xdoc::seetopic "<<" "total order on ACL2 values")
   ".")
  (if (emptyp x)
      nil
    (mv-let (k v)
        (head x)
      (update v k (inverse (tail x)))))
  :verify-guards :after-returns

  ///

  (defcong mequiv equal (inverse x) 1)

  (defrule keys-of-inverse-is-values
      (equal (keys (inverse x))
             (values x))
    :enable values)

  (defrule values-of-inverse-is-keys-when-injectivep
      (implies (injectivep x)
               (equal (values (inverse x))
                      (keys x)))
    :enable (assoc-to-in-of-keys
             injectivep-implies-unique-head-value))

  (defrule inverse-implies-injectivep
      (implies (injectivep x)
               (injectivep (inverse x)))
    :enable (injectivep
             in-of-keys-to-assoc))

  (defrule not-assoc-of-inverse-when-not-in-values
      (implies (and (injectivep x)
                    (not (set::in v (values x))))
               (not (assoc v (inverse x))))
    :enable assoc-to-in-of-keys)

  (defrulel assoc-of-inverse-when-assoc
      (implies (and (injectivep x)
                    (assoc v x)
                    (equal (cdr (assoc v x)) k))
               (equal (assoc k (inverse x))
                      (cons k v)))
    :enable (values
             injectivep-implies-unique-head-value)
    :use equal-val-implies-equal-key-when-injectivep)

  (defrule injectivep-implies-not-rlookup-head-val-tail
      (implies (injectivep x)
               (set::emptyp (rlookup (mv-nth 1 (head x))
                                     (tail x))))
    :enable (rlookup-to-in-of-values
             injectivep-implies-unique-head-value))

  (defrule assoc-of-inverse
      (implies (injectivep x)
               (equal (assoc k (inverse x))
                      (and (set::in k (values x))
                           (cons k (set::head (rlookup k x))))))
    :enable (rlookup values set::expensive-rules))

  (defruledl assoc-of-inverse-inverse
      (implies (injectivep x)
               (equal (assoc k (inverse (inverse x)))
                      (assoc k x)))
    :enable (injectivep
             set::expensive-rules
             rlookup-to-in-of-values
             in-of-keys-to-assoc))

  (defrule inverse-inverse-when-injectivep
      (implies (injectivep x)
               (equal (inverse (inverse x))
                      (mfix x)))
    :enable (assoc-of-inverse-inverse
             extensionality))

  (defruledl assoc-of-compose-inverse
      (implies (and (injectivep x)
                    (assoc k (compose (inverse x) x)))
               (equal (assoc k (compose (inverse x) x))
                      (cons k k)))
    :enable (rlookup-of-cdr-assoc-when-injectivep
             assoc-of-compose))

  (defrule identityp-compose-with-inverse
    (implies (injectivep x)
             (identityp (compose (inverse x) x)))
    :enable (assoc-of-compose-inverse
             pick-a-point-identityp))

  (defruled lookup-inverse-in-keys-when-in-values-and-injective
    (implies (and (injectivep map)
                  (set::in y (values map)))
             (set::in (lookup y (inverse map))
                      (keys map)))
    :enable (lookup
             in-of-values-to-rlookup
             set::expensive-rules)
    :use (:instance set::in-head (x (rlookup y map)))
    :disable set::in-head))

(in-theory (disable injectivep-implies-not-rlookup-head-val-tail))
