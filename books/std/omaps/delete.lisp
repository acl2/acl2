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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule assoc-of-delete
  (equal (assoc x (delete y map))
         (if (equal x y)
             nil
           (assoc x map)))
  :induct t
  :enable delete)

(defrule lookup-of-delete
  (equal (lookup x (delete y map))
         (if (equal x y)
             nil
           (lookup x map)))
  :enable lookup)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule delete-when-not-assoc
  (implies (not (assoc key map))
           (equal (delete key map)
                  (mfix map)))
  :enable (double-containment
           pick-a-point))

(defrule idempotency-of-delete
  (equal (delete key (delete key map))
         (delete key map)))

(defrule commutativity-of-delete
  (equal (delete y (delete x map))
         (delete x (delete y map)))
  :enable (double-containment
           pick-a-point))

(defrule delete-of-update
  (equal (delete key (update key val map))
         (delete key map))
  :enable (double-containment
           pick-a-point))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule submap-of-delete
  (submap (delete key map) map)
  :enable pick-a-point)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule keys-of-delete
  (equal (keys (delete key map))
         (set::delete key (keys map)))
  :enable set::expensive-rules)

(defruled size-of-delete
  (equal (size (delete key map))
         (if (assoc key map)
             (- (size map) 1)
           (size map)))
  :enable (size-to-cardinality-of-keys
           set::delete-cardinality))
