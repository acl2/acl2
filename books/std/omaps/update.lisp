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

(include-book "core")
(include-book "with-fixing-theorems")
(include-book "assoc")
(include-book "submap")
(include-book "delete")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled update-identity
  (implies (and (assoc key map)
                (equal (cdr (assoc key map)) val))
           (equal (update key val map)
                  map)))

(defrule update-identity-cheap
  (implies (and (equal (cdr (assoc key map)) val)
                (assoc key map))
           (equal (update key val map)
                  map))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :by update-identity)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule update-of-delete
  (equal (update key val (delete key map))
         (update key val map))
  :enable (double-containment
           pick-a-point))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled size-of-update
  (equal (size (update key val map))
         (if (assoc key map)
             (size map)
           (+ 1 (size map))))
  :enable (size-to-cardinality-of-keys
           set::insert-cardinality))
