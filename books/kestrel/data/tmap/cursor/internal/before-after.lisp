; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/tset/in-defs" :dir :system)
(include-book "kestrel/data/tset/min-max-defs" :dir :system)

(include-book "../../map-defs")
(include-book "../../keys-defs")
(include-book "../../lookup-defs")
(include-book "../../to-omap-defs")
(include-book "../cursor-defs")
(include-book "../before-after-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))

(local (include-book "kestrel/data/tset/min-max" :dir :system))

(local (include-book "kestrel/data/utilities/omap" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "kestrel/lists-light/last" :dir :system))

(local (include-book "../../map"))
(local (include-book "../../keys"))
(local (include-book "../../lookup"))
(local (include-book "../../update"))
(local (include-book "../../to-omap"))
(local (include-book "../cursor"))
(local (include-book "../before-after"))
(local (include-book "zip-side"))
(local (include-book "zip-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This book relates before and after to the zipper's sequences, for use in
;; the proofs of the other cursor books. All rules are disabled.

(defruled in-of-keys-of-before-becomes-assoc-equal
  (equal (tset::in key (keys (before cursor)))
         (and (assoc-equal key (zip-before (cursor-fix cursor)))
              t))
  :enable (before
           omap::in-of-keys-to-assoc))

(defruled in-of-keys-of-after-becomes-assoc-equal
  (equal (tset::in key (keys (after cursor)))
         (and (assoc-equal key (zip-after (cursor-fix cursor)))
              t))
  :enable (after
           omap::in-of-keys-to-assoc))

(defruled lookup-of-before-becomes-assoc-equal
  (equal (lookup key (before cursor) :default default)
         (if (assoc-equal key (zip-before (cursor-fix cursor)))
             (cdr (assoc-equal key (zip-before (cursor-fix cursor))))
           default))
  :enable (before
           zip-omap-before-becomes-zip-before
           bstp-of-zip-plug-of-cursor-fix
           data::omap-assoc-becomes-assoc-equal))

(defruled lookup-of-after-becomes-assoc-equal
  (equal (lookup key (after cursor) :default default)
         (if (assoc-equal key (zip-after (cursor-fix cursor)))
             (cdr (assoc-equal key (zip-after (cursor-fix cursor))))
           default))
  :enable (after
           zip-omap-after-becomes-zip-after
           bstp-of-zip-plug-of-cursor-fix
           data::omap-assoc-becomes-assoc-equal))

(defruled emptyp-of-before-becomes-not-consp
  (equal (emptyp (before cursor))
         (not (consp (zip-before (cursor-fix cursor)))))
  :enable before)

(defruled emptyp-of-after-becomes-not-consp
  (equal (emptyp (after cursor))
         (not (consp (zip-after (cursor-fix cursor)))))
  :enable after)

;;;;;;;;;;;;;;;;;;;;

(defruled zip-before-of-cursor-fix-becomes-to-omap-of-before
  (equal (zip-before (cursor-fix cursor))
         (to-omap (before cursor)))
  :enable (before
           zip-omap-before-becomes-zip-before
           bstp-of-zip-plug-of-cursor-fix))

(defruled zip-after-of-cursor-fix-becomes-to-omap-of-after
  (equal (zip-after (cursor-fix cursor))
         (to-omap (after cursor)))
  :enable (after
           zip-omap-after-becomes-zip-after
           bstp-of-zip-plug-of-cursor-fix))

;;;;;;;;;;;;;;;;;;;;

(defruled min-of-keys-of-after-becomes-caar-of-zip-after
  (equal (tset::min (keys (after cursor)))
         (caar (zip-after (cursor-fix cursor))))
  :enable (tset::equal-of-min-becomes-sk
           tset::not-<<-all-l-sk
           in-of-keys-of-after-becomes-assoc-equal
           emptyp-of-after-becomes-not-consp
           bstp-of-zip-plug-of-cursor-fix
           data::assoc-equal-of-caar
           data::car-under-iff-when-omapp
           data::not-<<-of-arg1-and-caar-when-assoc-equal))

(defruled max-of-keys-of-before-becomes-caar-of-last-of-zip-before
  (equal (tset::max (keys (before cursor)))
         (caar (last (zip-before (cursor-fix cursor)))))
  :enable (tset::equal-of-max-becomes-sk
           tset::not-<<-all-r-sk
           in-of-keys-of-before-becomes-assoc-equal
           emptyp-of-before-becomes-not-consp
           bstp-of-zip-plug-of-cursor-fix
           data::assoc-equal-of-caar-of-last-when-omapp
           data::car-of-last-under-iff-when-omapp
           data::not-<<-of-caar-of-last-when-assoc-equal))
