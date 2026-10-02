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

(local (include-book "assoc"))
(local (include-book "extensionality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compose ((x mapp) (y mapp))
  :returns (map mapp)
  :parents (omaps)
  :short "Compose two omaps as functions."
  :long
  (xdoc::topstring-p
   "Maps key @('k') to @('w') when @('y') maps @('k') to @('v')
    and @('x') maps @('v') to @('w').
    Keys of @('y') with no matching entry in @('x') are dropped.")
  (if (emptyp y)
      nil
    (mv-let (k v) (head y)
      (let ((pair (assoc v x)))
        (if pair
            (update k (cdr pair) (compose x (tail y)))
          (compose x (tail y))))))
  :verify-guards :after-returns

  ///

  (defcong mequiv equal (compose x y) 1)

  (defcong mequiv equal (compose x y) 2)

  (defrule assoc-of-compose
      (equal (assoc k (compose x y))
             (and (assoc k y)
                  (assoc (cdr (assoc k y)) x)
                  (cons k
                        (cdr (assoc (cdr (assoc k y)) x))))))

  (defruled lookup-of-compose
    (equal (lookup key (compose x y))
           (if (set::in key (keys y))
               (lookup (lookup key y) x)
             nil))
    :enable (lookup assoc-to-in-of-keys)
    :disable compose)

  (defruled values-of-compose
    (equal (values (compose x y))
           (lookup* (values y) x))
    :induct (compose x y)
    :enable (values lookup lookup*-of-insert))

  (defrule compose-associativity
      (equal (compose (compose x y) z)
             (compose x (compose y z)))
    :enable extensionality))

(in-theory (disable assoc-of-compose))
