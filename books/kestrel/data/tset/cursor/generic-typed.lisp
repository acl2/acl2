; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/defrule" :dir :system)

(include-book "../set-defs")
(include-book "../generic-typed-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "from-cursor-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "../generic-typed"))
(local (include-book "entry"))
(local (include-book "from-cursor"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A cursor carries no element type. This discharges the guard of a typed walk
;; at @(tsee entry), for a set whose elements are all generic.

(defrule genericp-of-entry-when-set-all-genericp
  (implies (and (set-all-genericp (from-cursor cursor))
                (entryp cursor))
           (genericp (entry cursor))))
