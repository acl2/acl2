; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/defrule" :dir :system)

(include-book "../map-defs")
(include-book "../keys-defs")
(include-book "../values-defs")
(include-book "../generic-typed")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "from-cursor-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "../keys"))
(local (include-book "../in"))
(local (include-book "../lookup"))
(local (include-book "entry"))
(local (include-book "from-cursor"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A cursor carries no key or value type. These discharge the guards of a
;; typed walk at @(tsee entry-key) and @(tsee entry-val), for a map whose keys
;; or values are all generic.

(defrule genericp-of-entry-key-when-set-all-genericp-of-keys
  (implies (and (tset::set-all-genericp (keys (from-cursor cursor)))
                (entryp cursor))
           (tset::genericp (entry-key cursor))))

(defrule genericp-of-entry-val-when-set-all-genericp-of-values
  (implies (and (tset::set-all-genericp (values (from-cursor cursor)))
                (entryp cursor))
           (tset::genericp (entry-val cursor)))
  :use (:instance genericp-of-lookup-when-set-all-genericp-of-values
                  (k (entry-key cursor))
                  (map (from-cursor cursor)))
  :disable genericp-of-lookup-when-set-all-genericp-of-values)
