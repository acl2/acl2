; Ordered Maps (Omaps) Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "std/util/defrule" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/alists-light/remove-assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))

(include-book "core")
(include-book "extensionality")
(include-book "delete")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-from-alist
  (equal (emptyp (from-alist alist))
         (not (consp alist)))
  :expand (from-alist alist))

(defrule assoc-of-from-alist
  (implies (alistp alist)
           (equal (assoc key (from-alist alist))
                  (assoc-equal key alist)))
  :induct t
  :enable (from-alist
           assoc-equal
           alistp))

(defrule from-alist-of-acons
  (equal (from-alist (acons key val alist))
         (update key val (from-alist alist)))
  :enable (from-alist
           acons))

(defruled update-of-from-alist-becomes-from-alist-of-acons
  (equal (update key val (from-alist alist))
         (from-alist (acons key val alist)))
  :by from-alist-of-acons)

(theory-invariant
  (incompatible! (:rewrite from-alist-of-acons)
                 (:rewrite update-of-from-alist-becomes-from-alist-of-acons)))

(defrule from-alist-of-cons
  (equal (from-alist (cons key-val alist))
         (update (car key-val) (cdr key-val) (from-alist alist)))
  :enable from-alist)

(theory-invariant
  (incompatible! (:rewrite from-alist-of-cons)
                 (:rewrite update-of-from-alist-becomes-from-alist-of-acons)))

(defrule from-alist-of-remove-assoc-equal
  (implies (alistp alist)
           (equal (from-alist (remove-assoc-equal key alist))
                  (delete key (from-alist alist))))
  :enable extensionality)

(defruled delete-of-from-alist-becomes-from-alist-of-remove-assoc-equal
  (implies (alistp alist)
           (equal (delete key (from-alist alist))
                  (from-alist (remove-assoc-equal key alist))))
  :enable extensionality)

(theory-invariant
  (incompatible! (:rewrite from-alist-of-remove-assoc-equal)
                 (:rewrite delete-of-from-alist-becomes-from-alist-of-remove-assoc-equal)))

(defrule keys-of-from-alist
  (implies (alistp alist)
           (equal (keys (from-alist alist))
                  (mergesort (strip-cars alist))))
  :enable (set::expensive-rules
           in-of-keys-to-assoc
           acl2::member-equal-of-strip-cars-iff))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled from-lists-becomes-from-alist
  (equal (from-lists keys vals)
         (from-alist (pairlis$ keys vals)))
  :induct t
  :enable (from-lists
           from-alist
           pairlis$))
