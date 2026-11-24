; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

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

(define entry-key ((cursor cursorp))
  :guard (entryp cursor)
  :parents (cursor)
  :short "The key of the entry a @(see cursor) is at."
  :long
  (xdoc::topstring-p
    "Logically, this is @('nil') at a hole.")
  (zip-key (cursor-fix cursor))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* entryp break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule entry-key-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (entry-key cursor0)
                  (entry-key cursor1)))
  :rule-classes :congruence
  :enable entry-key)

(defruled entry-key-when-not-entryp
  (implies (not (entryp cursor))
           (equal (entry-key cursor)
                  nil))
  :enable (entry-key
           entryp))

(defrule entry-key-when-not-entryp-cheap
  (implies (not (entryp cursor))
           (equal (entry-key cursor)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by entry-key-when-not-entryp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-val ((cursor cursorp))
  :guard (entryp cursor)
  :parents (cursor)
  :short "The value of the entry a @(see cursor) is at."
  :long
  (xdoc::topstring-p
    "Logically, this is @('nil') at a hole.")
  (zip-val (cursor-fix cursor))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* entryp break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule entry-val-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (entry-val cursor0)
                  (entry-val cursor1)))
  :rule-classes :congruence
  :enable entry-val)

(defruled entry-val-when-not-entryp
  (implies (not (entryp cursor))
           (equal (entry-val cursor)
                  nil))
  :enable (entry-val
           entryp))

(defrule entry-val-when-not-entryp-cheap
  (implies (not (entryp cursor))
           (equal (entry-val cursor)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by entry-val-when-not-entryp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry ((cursor cursorp))
  :guard (entryp cursor)
  :returns (mv key val)
  :parents (cursor)
  :short "The @(tsee entry-key) and @(tsee entry-val)."
  :long
  (xdoc::topstring-p
    "This function is enabled by default.")
  (mv (entry-key cursor) (entry-val cursor))
  :enabled t
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy entry-extra-rules
  '(entry-key-when-not-entryp
    entry-val-when-not-entryp))
