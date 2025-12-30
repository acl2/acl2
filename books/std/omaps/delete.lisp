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
(include-book "extensionality")
(include-book "compatiblep")

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

;;;;;;;;;;;;;;;;;;;;

(defrule assoc-of-delete*
  (equal (assoc key (delete* keys map))
         (if (set::in key keys)
             nil
           (assoc key map)))
  :induct t
  :enable delete*)

(defrule lookup-of-delete*
  (equal (lookup key (delete* keys map))
         (if (set::in key keys)
             nil
           (lookup key map)))
  :enable lookup)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule delete-when-not-assoc
  (implies (not (assoc key map))
           (equal (delete key map)
                  (mfix map)))
  :enable extensionality)

(defrule idempotence-of-delete
  (equal (delete key (delete key map))
         (delete key map)))

(defrule commutativity-of-delete
  (equal (delete y (delete x map))
         (delete x (delete y map)))
  :enable extensionality)

(defrule delete-of-update
  (equal (delete key (update key val map))
         (delete key map))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule submap-of-delete
  (submap (delete key map) map)
  :enable pick-a-point)

(defrule submap-of-delete*
  (submap (delete* key map) map)
  :enable pick-a-point)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule compatiblep-of-delete
  (implies (compatiblep map0 map1)
           (compatiblep map0 (delete key map1))))

(defrule compatiblep-of-delete-same
  (compatiblep map (delete key map)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule keys-of-delete
  (equal (keys (delete key map))
         (set::delete key (keys map)))
  :enable (set::expensive-rules
           in-of-keys-to-assoc))

(defrule keys-of-delete*
  (equal (keys (delete* keys map))
         (difference (keys map) keys))
  :enable (set::expensive-rules
           in-of-keys-to-assoc))

;;;;;;;;;;;;;;;;;;;;

(defruled size-of-delete
  (equal (size (delete key map))
         (if (assoc key map)
             (- (size map) 1)
           (size map)))
  :enable (size-to-cardinality-of-keys
           set::delete-cardinality
           in-of-keys-to-assoc))

(defrule size-of-delete-linear
  (<= (size (delete key map))
      (size map))
  :rule-classes :linear
  :enable size-of-delete)

(defrule size-of-delete-when-assoc-linear
  (implies (assoc key map)
           (< (size (delete key map))
              (size map)))
  :rule-classes :linear
  :enable size-of-delete)

(defrule size-of-delete*-linear
  (<= (size (delete* keys map))
      (size map))
  :rule-classes :linear
  :induct t
  :enable delete*)
