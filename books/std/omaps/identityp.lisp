; Ordered Maps (Omaps) Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "std/util/define-sk" :dir :system)

(include-book "core")
(include-book "compose")

(local (include-book "assoc"))
(local (include-book "extensionality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identityp ((x mapp))
  :returns (yes/no booleanp)
  :parents (omaps)
  :short "Check if an omap is an identity map."
  :long
  (xdoc::topstring-p
   "An omap where every key maps to itself.
    Defined recursively: the empty map is an identity map,
    and a non-empty map is an identity map iff its head key equals its head value
    and its tail is also an identity map.")
  (or (emptyp x)
      (mv-let (k v) (head x)
        (and (equal k v)
             (identityp (tail x)))))
  
  ///

  (defcong mequiv equal (identityp x) 1)

  (defrule values-is-keys-when-identityp
    (implies (identityp x)
             (equal (values x)
                    (keys x)))
  :enable (values keys))

  (defrule assoc-when-identityp
      (implies (and (identityp x)
                    (assoc k x))
               (equal (assoc k x)
                      (cons k k))))

  (defrulel equal-keys-and-not-assoc-X-implies-not-assoc-Y
      (implies (and (equal (keys x) (keys y))
                    (not (assoc k x)))
               (not (assoc k y)))
    :enable assoc-to-in-of-keys
    :rule-classes :forward-chaining)

  (defruledl equal-assoc-when-identityp-and-equal-keys
      (implies (and (identityp x)
                    (identityp y)
                    (equal (keys x)
                           (keys y)))
               (equal (assoc k x)
                      (assoc k y)))
    :enable assoc-to-in-of-keys
    :cases ((assoc k x)))

  (defruled equal-when-identityp-and-equal-keys
      (implies (and (identityp x)
                    (identityp y)
                    (mapp x)
                    (mapp y)
                    (equal (keys x)
                           (keys y)))
               (equal x y))
    :enable extensionality
    :use (:instance equal-assoc-when-identityp-and-equal-keys
                    (k (ext-equal-witness x y)))
    :rule-classes :forward-chaining)

  (defruledl compose-is-restrict-when-Y-identityp-helper
      (implies (identityp y)
               (equal (assoc k (compose x y))
                      (assoc k (restrict (keys y) x))))
    :enable (assoc assoc-of-restrict in-of-keys-to-assoc))

  (defruled compose-is-restrict-when-Y-identityp
      (implies (identityp y)
               (equal (compose x y)
                      (restrict (keys y) x)))
    :enable (compose-is-restrict-when-Y-identityp-helper
             extensionality))

  (defrule self-compose-is-self-when-identityp
      (implies (and (identityp x)
                    (mapp x))
               (equal (compose x x) x))
    :enable extensionality))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk identityp-sk ((x mapp))
  (forall (k)
          (implies (assoc k x)
                   (equal (assoc k x)
                          (cons k k))))
  :skolem-name identityp-witness)

(defruledl identityp-sk-of-tail-when-identityp-sk
    (implies (identityp-sk x)
             (identityp-sk (tail x)))
  :expand (identityp-sk (tail x))
  :use (:instance identityp-sk-necc
                  (k (identityp-witness (tail x)))))

(defruled identityp-sk-when-identityp
    (implies (identityp x)
             (identityp-sk x))
  :enable identityp-sk)

(defruled identityp-when-identityp-sk
    (implies (and (identityp-sk x)
                  (mapp x))
             (identityp x))
  :hints ('(:use (:instance identityp-sk-necc
                            (k (mv-nth 0 (head x))))))
  :enable (identityp
           identityp-sk-of-tail-when-identityp-sk))

(defsection pick-a-point-identityp
  :parents (identityp)
  :short "A theory to enable pick-a-point reasoning for @(tsee identityp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Analogous to the @(see pick-a-point) theory for @(tsee submap).
     Rewrites @(tsee identityp) to the skolem-equivalent @(tsee identityp-sk)
     to expose the arbitrary element for point-wise reasoning."))

  (defruled identityp-to-identityp-sk
      (implies (mapp x)
               (equal (identityp x)
                      (identityp-sk x)))
    :use (identityp-sk-when-identityp
          identityp-when-identityp-sk))

  (defthy pick-a-point-identityp
    '(identityp-to-identityp-sk
      identityp-sk)))
