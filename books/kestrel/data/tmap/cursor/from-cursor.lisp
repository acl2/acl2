; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/tset/in-defs" :dir :system)

(include-book "../map-defs")
(include-book "../keys-defs")
(include-book "../lookup-defs")
(include-book "../submap-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/in" :dir :system))

(local (include-book "../internal/keys"))
(local (include-book "../internal/lookup"))
(local (include-book "../map"))
(local (include-book "../keys"))
(local (include-book "../lookup"))
(local (include-book "../submap"))
(local (include-book "cursor"))
(local (include-book "entry"))

(local (include-book "internal/before-after"))
(local (include-book "internal/zip-side"))
(local (include-book "internal/zip-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-cursor ((cursor cursorp))
  :returns (map mapp
                :hints (("Goal" :in-theory (enable* break-abstraction))))
  :parents (cursor)
  :short "The underlying @(see tmap) of a @(see cursor)."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(\\log(n))$).")
  (zip-plug (cursor-fix cursor))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule from-cursor-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (from-cursor cursor0)
                  (from-cursor cursor1)))
  :rule-classes :congruence
  :enable from-cursor)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl in-of-keys-of-from-cursor-becomes-in-of-tree-key-set
  (equal (tset::in key (keys (from-cursor cursor)))
         (tset::in key (tree-key-set (zip-plug (cursor-fix cursor)))))
  :enable (keys
           from-cursor
           break-abstraction))

(defruledl lookup-of-from-cursor-becomes-tree-lookup
  (equal (lookup key (from-cursor cursor) :default default)
         (if (tset::in key (tree-key-set (zip-plug (cursor-fix cursor))))
             (tree-lookup key (zip-plug (cursor-fix cursor)))
           default))
  :enable (lookup
           keys
           from-cursor
           break-abstraction))

(defruled in-of-keys-of-from-cursor-becomes-in-of-keys-of-before-or-entry-key-or-after
  (equal (tset::in key (keys (from-cursor cursor)))
         (or (tset::in key (keys (before cursor)))
             (and (entryp cursor)
                  (equal key (entry-key cursor)))
             (tset::in key (keys (after cursor)))))
  :enable (in-of-keys-of-before-becomes-assoc-equal
           in-of-keys-of-after-becomes-assoc-equal
           in-of-keys-of-from-cursor-becomes-in-of-tree-key-set
           in-of-tree-key-set-of-zip-plug-split-at-cursor
           entry-key
           entryp))

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-entry-key-and-keys-of-from-cursor
  (implies (entryp cursor)
           (tset::in (entry-key cursor) (keys (from-cursor cursor))))
  :enable in-of-keys-of-from-cursor-becomes-in-of-keys-of-before-or-entry-key-or-after)

(defrule lookup-of-entry-key-and-from-cursor
  (implies (entryp cursor)
           (equal (lookup (entry-key cursor) (from-cursor cursor)
                          :default default)
                  (entry-val cursor)))
  :enable (lookup-of-from-cursor-becomes-tree-lookup
           entry-key
           entry-val
           entryp
           break-abstraction))

(defruled lookup-of-from-cursor-becomes-lookup-of-before-or-entry-val-or-after
  (equal (lookup key (from-cursor cursor) :default default)
         (cond ((tset::in key (keys (before cursor)))
                (lookup key (before cursor) :default default))
               ((and (entryp cursor)
                     (equal key (entry-key cursor)))
                (entry-val cursor))
               (t (lookup key (after cursor) :default default))))
  :enable (lookup-of-from-cursor-becomes-tree-lookup
           in-of-keys-of-before-becomes-assoc-equal
           lookup-of-before-becomes-assoc-equal
           lookup-of-after-becomes-assoc-equal
           in-of-tree-key-set-of-zip-plug-split-at-cursor
           assoc-equal-of-zip-before-when-assoc-equal-and-bstp
           assoc-equal-of-zip-after-when-assoc-equal-and-bstp
           entry-key
           entry-val
           entryp
           break-abstraction))

(defrule submap-of-before-and-from-cursor
  (submap (before cursor) (from-cursor cursor))
  :enable (submap-becomes-submap-sk
           submap-sk
           in-of-keys-of-before-becomes-assoc-equal
           lookup-of-before-becomes-assoc-equal
           lookup-of-from-cursor-becomes-tree-lookup
           in-of-tree-key-set-of-zip-plug-split-at-cursor
           assoc-equal-of-zip-before-when-assoc-equal-and-bstp
           break-abstraction))

(defrule submap-of-after-and-from-cursor
  (submap (after cursor) (from-cursor cursor))
  :enable (submap-becomes-submap-sk
           submap-sk
           in-of-keys-of-after-becomes-assoc-equal
           lookup-of-after-becomes-assoc-equal
           lookup-of-from-cursor-becomes-tree-lookup
           in-of-tree-key-set-of-zip-plug-split-at-cursor
           assoc-equal-of-zip-after-when-assoc-equal-and-bstp
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy from-cursor-extra-rules
  '(in-of-keys-of-from-cursor-becomes-in-of-keys-of-before-or-entry-key-or-after
    lookup-of-from-cursor-becomes-lookup-of-before-or-entry-val-or-after))
