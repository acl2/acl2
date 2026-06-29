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

(local (include-book "assoc"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define injectivep ((x mapp))
  :parents (omaps)
  :returns (yes/no booleanp)
  :short "Check if an omap is injective."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, different keys are mapped to different values.
     We express this via a recursion:
     the empty map is injective;
     a non-empty map is injective iff
     the value of its first key is not among the values of the tail of the map,
     and the tail of the map is itself injective.")
   (xdoc::p
    "The @(':exec') version checks injectivity by comparing cardinalities:
     an omap is injective iff it has the same number of distinct keys
     as distinct values.
     This is more efficient for execution than the recursive membership checks
     in the @(':logic') version."))
  (mbe :logic
       (or (emptyp x)
           (b* (((mv & v) (head x)))
             (and (not (set::in v (values (tail x))))
                  (injectivep (tail x)))))
       :exec (equal (cardinality (keys x))
                    (cardinality (values x))))
  :verify-guards nil ;; Verified below

  ///

  (defcong mequiv equal (injectivep x) 1)

  (defrule injectivep-implies-injectivep-tail
      (implies (injectivep x)
               (injectivep (tail x))))

  (defruled injectivep-implies-unique-head-value
      (implies (injectivep x)
               (not (set::in (mv-nth 1 (head x))
                             (values (tail x))))))

  (defruled head-val-is-not-assoc-tail-when-injectivep
      (implies (and (injectivep x)
                    (assoc k (tail x)))
               (not (equal (mv-nth 1 (head x))
                           (cdr (assoc k (tail x)))))))

  (defruled equal-val-implies-equal-key-when-injectivep
      (implies (and (injectivep x)
                    (assoc k1 x)
                    (assoc k2 x)
                    (equal (cdr (assoc k1 x))
                           (cdr (assoc k2 x))))
               (equal k1 k2))
    :enable assoc
    :rule-classes :forward-chaining)

  (defrulel injectivep-implies-equal-cardinality-keys-values
      (implies (injectivep x)
               (equal (cardinality (keys x))
                      (cardinality (values x))))
    :enable (keys values set::expensive-rules)
    :rule-classes :forward-chaining)

  (defrulel equal-cardinality-keys-values-implies-injectivep
      (implies (equal (cardinality (keys x))
                      (cardinality (values x)))
               (injectivep x))
    :enable (keys values set::expensive-rules)
    :rule-classes :type-prescription)

  (defruled injectivep-to-cardinality-of-keys-and-values
      (equal (injectivep x)
             (equal (cardinality (keys x))
                    (cardinality (values x)))))

  (defruled cardinality-of-keys-and-values-to-injectivep
      (equal (equal (cardinality (keys x))
                    (cardinality (values x)))
             (injectivep x)))

  (theory-invariant (incompatible (:rewrite injectivep-to-cardinality-of-keys-and-values)
                                  (:rewrite cardinality-of-keys-and-values-to-injectivep)))

  (verify-guards injectivep
      :hints (("Goal" :in-theory
                      (enable cardinality-of-keys-and-values-to-injectivep))))

  (defruled identityp-implies-injectivep
      (implies (identityp x)
               (injectivep x))
    :enable injectivep-to-cardinality-of-keys-and-values
    :use values-is-keys-when-identityp
    :rule-classes :forward-chaining)

  (defruled rlookup-of-cdr-assoc-when-injectivep
      (implies (and (injectivep x)
                    (assoc k x))
               (equal (rlookup (cdr (assoc k x)) x)
                      (insert k nil)))
    :enable (rlookup
             in-of-values-to-rlookup))

  (defruledl cardinality-of-keys-and-values-when-not-in-keys-and-values
      (implies (and (injectivep x)
                    (not (set::in k (keys x)))
                    (not (set::in v (values x))))
               (equal (cardinality (keys (update k v x)))
                      (cardinality (values (update k v x)))))
    :enable (injectivep-to-cardinality-of-keys-and-values
             assoc-to-in-of-keys
             set::expensive-rules))

  (defrule injectivep-of-update-when-not-in-keys-and-values
      (implies (and (injectivep x)
                    (not (set::in k (keys x)))
                    (not (set::in v (values x))))
               (injectivep (update k v x)))
    :use (cardinality-of-keys-and-values-when-not-in-keys-and-values
          (:instance cardinality-of-keys-and-values-to-injectivep
                     (x (update k v x))))))
