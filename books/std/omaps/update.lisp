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
(local (include-book "assoc"))
(local (include-book "submap"))
(local (include-book "extensionality"))
(local (include-book "compatiblep"))
(local (include-book "delete"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled update-redundant
  (implies (and (assoc key map)
                (equal (cdr (assoc key map)) val))
           (equal (update key val map)
                  map)))

(defrule update-redundant-cheap
  (implies (and (equal (cdr (assoc key map)) val)
                (assoc key map))
           (equal (update key val map)
                  map))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :by update-redundant)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule update-of-delete
  (equal (update key val (delete key map))
         (update key val map))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule rlookup-of-update-same
  (equal (rlookup val (update key val map))
         (set::insert key (rlookup val map)))
  :enable set::expensive-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled size-of-update
  (equal (size (update key val map))
         (if (assoc key map)
             (size map)
           (+ 1 (size map))))
  :enable (size-to-cardinality-of-keys
           set::insert-cardinality
           in-of-keys-to-assoc))

(defrule size-of-update-linear
  (<= (size map)
      (size (update key val map)))
  :rule-classes :linear
  :enable size-of-update)

(defrule size-of-update-when-not-assoc-linear
  (implies (not (assoc key map))
           (< (size map)
              (size (update key val map))))
  :rule-classes :linear
  :enable size-of-update)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl equal-of-delete-implies-equal-of-assoc-update
  (implies (and (mapp y)
                (assoc k1 y)
                (equal (cdr (assoc k1 y)) v)
                (equal (delete k1 x)
                       (delete k1 y)))
           (equal (assoc k2 (update k1 v x))
                  (assoc k2 y)))
  :enable cons-of-key-and-cdr-assoc
  :use (:instance assoc-of-delete
                   (x k2)
                   (y k1)
                   (map y)))

(defruledl equal-of-delete-implies-equal-of-update
  (implies (and (mapp y)
                (assoc k y)
                (equal (cdr (assoc k y)) v)
                (equal (delete k x)
                       (delete k y)))
           (equal (update k v x) y))
  :enable (equal-of-delete-implies-equal-of-assoc-update
           extensionality))

(defruled equal-of-update-is-equal-of-delete
  (equal (equal (update k v x) y)
         (and (mapp y)
              (assoc k y)
              (equal (cdr (assoc k y)) v)
              (equal (delete k x)
                     (delete k y))))
  :use equal-of-delete-implies-equal-of-update)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule idempotence-of-update*
  (equal (update* map map)
         (mfix map))
  :enable extensionality)

(defrule associativity-of-update*
  (equal (update* (update* x y) z)
         (update* x (update* y z)))
  :enable extensionality)

(defrule commutativity-of-update*-when-compatiblep
  (implies (compatiblep map0 map1)
           (equal (update* map1 map0)
                  (update* map0 map1)))
  :enable extensionality)

(defrule commutativity-2-of-update*-when-compatiblep
  (implies (compatiblep x y)
           (equal (update* y (update* x z))
                  (update* x (update* y z))))
  :enable extensionality)

(defrule update*-of-update
  (equal (update* (update key val map0) map1)
         (update key val (update* map0 map1)))
  :enable extensionality)

(defrule update*-of-delete-when-not-assoc
  (implies (not (assoc key map1))
           (equal (update* (delete key map0) map1)
                  (delete key (update* map0 map1))))
  :enable extensionality)

(defrule update*-of-arg1-and-delete-when-not-assoc
  (implies (not (assoc key map0))
           (equal (update* map0 (delete key map1))
                  (delete key (update* map0 map1))))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule submap-of-arg1-and-update*-of-arg1
  (submap x (update* x y))
  :enable pick-a-point)

(defrule submap-of-arg1-and-update*-of-arg2-when-compatiblep
  (implies (compatiblep x y)
           (submap x (update* y x))))

;;;;;;;;;;;;;;;;;;;;

(defrule update*-when-submap
  (implies (submap x y)
           (equal (update* x y)
                  (mfix y)))
  :enable extensionality)

(defrule update*-when-submap-2
  (implies (submap y x)
           (equal (update* x y)
                  (mfix x)))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule update*-of-update*-same
  (equal (update* x (update* x y))
         (update* x y)))
