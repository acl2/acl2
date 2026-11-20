; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "../set-defs")
(include-book "../in-defs")
(include-book "../to-oset-defs")
(include-book "../insert-defs")
(include-book "cursor-defs")
(include-book "internal/zip-side-defs")
(include-book "entry-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/utilities/oset" :dir :system))

(local (include-book "../set"))
(local (include-book "../in"))
(local (include-book "../insert"))
(local (include-book "../extensionality"))
(local (include-book "cursor"))
(local (include-book "entry"))

(local (include-book "internal/zip-side"))
(local (include-book "internal/zip-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

(defruledl zip-tree-before-becomes-from-oset
  (implies (setp (zip-plug zip))
           (equal (zip-tree-before zip)
                  (from-oset (zip-oset-before zip))))
  :enable (extensionality
           setp
           in))

(defruledl zip-tree-after-becomes-from-oset
  (implies (setp (zip-plug zip))
           (equal (zip-tree-after zip)
                  (from-oset (zip-oset-after zip))))
  :enable (extensionality
           setp
           in))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define before ((cursor cursorp))
  :returns (set setp)
  :parents (cursor)
  :short "The @(see tset) of elements before a @(see cursor)."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(\\log(n))$).")
  (mbe :logic (from-oset (zip-oset-before (cursor-fix cursor)))
       :exec (zip-tree-before (cursor-fix cursor)))
  :guard-hints (("Goal" :in-theory (enable* zip-tree-before-becomes-from-oset
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule before-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (before cursor0)
                  (before cursor1)))
  :rule-classes :congruence
  :enable before)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define after ((cursor cursorp))
  :returns (set setp)
  :parents (cursor)
  :short "The @(see tset) of elements after a @(see cursor)."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(\\log(n))$).")
  (mbe :logic (from-oset (zip-oset-after (cursor-fix cursor)))
       :exec (zip-tree-after (cursor-fix cursor)))
  :guard-hints (("Goal" :in-theory (enable* zip-tree-after-becomes-from-oset
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule after-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (after cursor0)
                  (after cursor1)))
  :rule-classes :congruence
  :enable after)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled <<-when-in-of-before-and-in-of-after
  (implies (and (in x (before cursor))
                (in y (after cursor)))
           (<< x y))
  :enable (before
           after
           <<-when-member-equal-of-zip-before-and-zip-after
           break-abstraction))

(defrule <<-of-entry-when-in-of-after
  (implies (and (entryp cursor)
                (in x (after cursor)))
           (<< (entry cursor) x))
  :enable (after
           entry
           entryp
           break-abstraction
           in-of-zip-oset-after-when-bstp)
  :disable in-of-zip-oset-after)

(defrule <<-of-arg1-and-entry-when-in-of-before
  (implies (and (entryp cursor)
                (in x (before cursor)))
           (<< x (entry cursor)))
  :enable (before
           entry
           entryp
           break-abstraction
           in-of-zip-oset-before-when-bstp)
  :disable in-of-zip-oset-before)

;;;;;;;;;;;;;;;;;;;;

(defrule not-in-of-entry-and-before
  (implies (entryp cursor)
           (not (in (entry cursor) (before cursor))))
  :use (:instance <<-of-arg1-and-entry-when-in-of-before (x (entry cursor)))
  :disable <<-of-arg1-and-entry-when-in-of-before
  :enable data::<<-rules)

(defrule not-in-of-entry-and-after
  (implies (entryp cursor)
           (not (in (entry cursor) (after cursor))))
  :use (:instance <<-of-entry-when-in-of-after (x (entry cursor)))
  :disable <<-of-entry-when-in-of-after
  :enable data::<<-rules)

(defruled not-in-of-after-when-in-of-before
  (implies (in x (before cursor))
           (not (in x (after cursor))))
  :use (:instance <<-when-in-of-before-and-in-of-after (y x))
  :enable data::<<-rules)

(defrule not-in-of-after-when-in-of-before-forward-chaining
  (implies (in x (before cursor))
           (not (in x (after cursor))))
  :rule-classes :forward-chaining
  :by not-in-of-after-when-in-of-before)

(defruled not-in-of-before-when-in-of-after
  (implies (in x (after cursor))
           (not (in x (before cursor))))
  :use (:instance <<-when-in-of-before-and-in-of-after (y x))
  :enable data::<<-rules)

(defrule not-in-of-before-when-in-of-after-forward-chaining
  (implies (in x (after cursor))
           (not (in x (before cursor))))
  :rule-classes :forward-chaining
  :by not-in-of-before-when-in-of-after)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy before-after-extra-rules
  '(<<-when-in-of-before-and-in-of-after
    not-in-of-after-when-in-of-before
    not-in-of-before-when-in-of-after))
