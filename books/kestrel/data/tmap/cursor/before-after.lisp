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
(include-book "../update-defs")
(include-book "cursor-defs")
(include-book "internal/zip-side-defs")
(include-book "entry-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))

(local (include-book "kestrel/data/utilities/omap" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "../map"))
(local (include-book "../keys"))
(local (include-book "../update"))
(local (include-book "../to-omap"))
(local (include-book "cursor"))
(local (include-book "entry"))

(local (include-book "internal/zip-side"))
(local (include-book "internal/zip-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

(defruledl zip-tree-before-becomes-from-omap
  (implies (mapp (zip-plug zip))
           (equal (zip-tree-before zip)
                  (from-omap (zip-omap-before zip))))
  :use (:instance from-omap-of-to-omap
                  (map (zip-tree-before zip)))
  :enable (to-omap
           mapp
           zip-omap-before-becomes-zip-before))

(defruledl zip-tree-after-becomes-from-omap
  (implies (mapp (zip-plug zip))
           (equal (zip-tree-after zip)
                  (from-omap (zip-omap-after zip))))
  :use (:instance from-omap-of-to-omap
                  (map (zip-tree-after zip)))
  :enable (to-omap
           mapp
           zip-omap-after-becomes-zip-after))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define before ((cursor cursorp))
  :returns (map mapp)
  :parents (cursor)
  :short "The @(see tmap) of entries before a @(see cursor)."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(\\log(n))$).")
  (mbe :logic (from-omap (zip-omap-before (cursor-fix cursor)))
       :exec (zip-tree-before (cursor-fix cursor)))
  :guard-hints (("Goal" :in-theory (enable* zip-tree-before-becomes-from-omap
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
  :returns (map mapp)
  :parents (cursor)
  :short "The @(see tmap) of entries after a @(see cursor)."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(\\log(n))$).")
  (mbe :logic (from-omap (zip-omap-after (cursor-fix cursor)))
       :exec (zip-tree-after (cursor-fix cursor)))
  :guard-hints (("Goal" :in-theory (enable* zip-tree-after-becomes-from-omap
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule after-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (after cursor0)
                  (after cursor1)))
  :rule-classes :congruence
  :enable after)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl in-of-keys-of-before-becomes-assoc-equal
  (equal (tset::in key (keys (before cursor)))
         (and (assoc-equal key (zip-before (cursor-fix cursor)))
              t))
  :enable (before
           omap::in-of-keys-to-assoc))

(defruledl in-of-keys-of-after-becomes-assoc-equal
  (equal (tset::in key (keys (after cursor)))
         (and (assoc-equal key (zip-after (cursor-fix cursor)))
              t))
  :enable (after
           omap::in-of-keys-to-assoc))

;;;;;;;;;;;;;;;;;;;;

(defruled <<-when-in-of-keys-of-before-and-in-of-keys-of-after
  (implies (and (tset::in x (keys (before cursor)))
                (tset::in y (keys (after cursor))))
           (<< x y))
  :enable (in-of-keys-of-before-becomes-assoc-equal
           in-of-keys-of-after-becomes-assoc-equal
           <<-when-assoc-equal-of-zip-before-and-zip-after
           break-abstraction))

(defrule <<-of-entry-key-when-in-of-keys-of-after
  (implies (and (entryp cursor)
                (tset::in key (keys (after cursor))))
           (<< (entry-key cursor) key))
  :enable (in-of-keys-of-after-becomes-assoc-equal
           entry-key
           entryp
           break-abstraction))

(defrule <<-of-arg1-and-entry-key-when-in-of-keys-of-before
  (implies (and (entryp cursor)
                (tset::in key (keys (before cursor))))
           (<< key (entry-key cursor)))
  :enable (in-of-keys-of-before-becomes-assoc-equal
           entry-key
           entryp
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;

(defrule not-in-of-keys-of-entry-key-and-before
  (implies (entryp cursor)
           (not (tset::in (entry-key cursor) (keys (before cursor)))))
  :use (:instance <<-of-arg1-and-entry-key-when-in-of-keys-of-before
                  (key (entry-key cursor)))
  :disable <<-of-arg1-and-entry-key-when-in-of-keys-of-before
  :enable data::<<-rules)

(defrule not-in-of-keys-of-entry-key-and-after
  (implies (entryp cursor)
           (not (tset::in (entry-key cursor) (keys (after cursor)))))
  :use (:instance <<-of-entry-key-when-in-of-keys-of-after
                  (key (entry-key cursor)))
  :disable <<-of-entry-key-when-in-of-keys-of-after
  :enable data::<<-rules)

(defruled not-in-of-keys-of-after-when-in-of-keys-of-before
  (implies (tset::in key (keys (before cursor)))
           (not (tset::in key (keys (after cursor)))))
  :use (:instance <<-when-in-of-keys-of-before-and-in-of-keys-of-after
                  (x key)
                  (y key))
  :enable data::<<-rules)

(defrule not-in-of-keys-of-after-when-in-of-keys-of-before-forward-chaining
  (implies (tset::in key (keys (before cursor)))
           (not (tset::in key (keys (after cursor)))))
  :rule-classes :forward-chaining
  :by not-in-of-keys-of-after-when-in-of-keys-of-before)

(defruled not-in-of-keys-of-before-when-in-of-keys-of-after
  (implies (tset::in key (keys (after cursor)))
           (not (tset::in key (keys (before cursor)))))
  :use (:instance <<-when-in-of-keys-of-before-and-in-of-keys-of-after
                  (x key)
                  (y key))
  :enable data::<<-rules)

(defrule not-in-of-keys-of-before-when-in-of-keys-of-after-forward-chaining
  (implies (tset::in key (keys (after cursor)))
           (not (tset::in key (keys (before cursor)))))
  :rule-classes :forward-chaining
  :by not-in-of-keys-of-before-when-in-of-keys-of-after)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy before-after-extra-rules
  '(<<-when-in-of-keys-of-before-and-in-of-keys-of-after
    not-in-of-keys-of-after-when-in-of-keys-of-before
    not-in-of-keys-of-before-when-in-of-keys-of-after))
