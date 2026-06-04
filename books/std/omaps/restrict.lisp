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
(local (include-book "update"))
(local (include-book "delete"))
(local (include-book "compatiblep"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule restrict-of-insert
    (equal (restrict (insert k ks) x)
           (if (assoc k x)
               (update k (cdr (assoc k x))
                       (restrict ks x))
             (restrict ks x)))
  :enable (restrict
           not-head-key-when-assoc-of-tail))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move
(defruledl intersect-of-insert-when-in
    (implies (set::in a y)
             (equal (intersect (insert a x) y)
                    (insert a (intersect x y))))
  :enable set::expensive-rules)

(defrulel compatiblep-implies-equal-restrict-intersect-keys
    (implies (compatiblep x y)
             (equal (restrict (intersect (keys x) (keys y)) x)
                    (restrict (intersect (keys x) (keys y)) y)))
  :enable (assoc-of-restrict extensionality)
  :rule-classes :forward-chaining)

(defrulel equal-restrict-intersect-keys-implies-compatiblep
    (implies (equal (restrict (intersect (keys x) (keys y)) x)
                    (restrict (intersect (keys x) (keys y)) y))
             (compatiblep x y))
  :enable (restrict
           compatiblep
           set::expensive-rules
           intersect-of-insert-when-in
           assoc-of-restrict
           in-of-keys-to-assoc
           equal-of-update-is-equal-of-delete)
  :rule-classes :forward-chaining)

(defruled compatiblep-is-equal-restrict-intersect-keys
    (equal (compatiblep x y)
           (equal (restrict (intersect (keys x) (keys y)) x)
                  (restrict (intersect (keys x) (keys y)) y))))
