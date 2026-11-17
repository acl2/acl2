; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "cursor-defs")
(include-book "internal/zip-side-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "../internal/tree"))
(local (include-book "cursor"))

(local (include-book "internal/zipper"))
(local (include-book "internal/zip-side"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entryp ((cursor cursorp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (cursor)
  :short "Check whether a @(see cursor) is at an entry, rather than a hole."
  (not (tree-empty-p (zip->focus (cursor-fix cursor))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule entryp-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (entryp cursor0)
                  (entryp cursor1)))
  :rule-classes :congruence
  :enable entryp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry ((cursor cursorp))
  :guard (entryp cursor)
  :parents (cursor)
  :short "The entry a @(see cursor) is at."
  :long
  (xdoc::topstring-p
    "Logically, this is @('nil') at a hole.")
  (zip-value (cursor-fix cursor))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* entryp break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule entry-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (entry cursor0)
                  (entry cursor1)))
  :rule-classes :congruence
  :enable entry)

(defruled entry-when-not-entryp
  (implies (not (entryp cursor))
           (equal (entry cursor)
                  nil))
  :enable (entry
           entryp))

(defrule entry-when-not-entryp-cheap
  (implies (not (entryp cursor))
           (equal (entry cursor)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by entry-when-not-entryp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy entry-extra-rules
  '(entry-when-not-entryp))
