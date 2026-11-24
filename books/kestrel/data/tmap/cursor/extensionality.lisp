; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "../internal/tree"))
(local (include-book "../map"))
(local (include-book "../update"))
(local (include-book "../to-omap"))
(local (include-book "cursor"))
(local (include-book "entry"))
(local (include-book "before-after"))
(local (include-book "internal/before-after"))
(local (include-book "from-cursor"))

(local (include-book "internal/zipper"))
(local (include-book "internal/zip-side"))
(local (include-book "internal/zip-uniqueness"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A map is determined by its omap, and the omap of a cursor's map is the
;; sequence of its view.

(defruledl to-omap-of-from-cursor
  (equal (to-omap (from-cursor cursor))
         (append (to-omap (before cursor))
                 (if (entryp cursor)
                     (cons (cons (entry-key cursor)
                                 (entry-val cursor))
                           (to-omap (after cursor)))
                   (to-omap (after cursor)))))
  :enable (to-omap
           from-cursor
           entryp
           entry-key
           entry-val
           tree-in-order-of-zip-plug-split-at-cursor
           zip-key+val-becomes-cons-of-zip-key-and-zip-val
           zip-before-of-cursor-fix-becomes-to-omap-of-before
           zip-after-of-cursor-fix-becomes-to-omap-of-after
           break-abstraction))

(defruledl equal-of-from-cursor-when-equal-of-view
  (implies (and (equal (entryp x) (entryp y))
                (equal (before x) (before y))
                (equal (entry-key x) (entry-key y))
                (equal (entry-val x) (entry-val y))
                (equal (after x) (after y)))
           (equal (from-cursor x)
                  (from-cursor y)))
  :use ((:instance from-omap-of-to-omap (map (from-cursor x)))
        (:instance from-omap-of-to-omap (map (from-cursor y))))
  :enable to-omap-of-from-cursor
  :disable from-omap-of-to-omap)

(defruledl equal-of-cursors
  (implies (and (cursorp x)
                (cursorp y))
           (equal (equal x y)
                  (and (equal (entryp x) (entryp y))
                       (equal (before x) (before y))
                       (equal (entry-key x) (entry-key y))
                       (equal (entry-val x) (entry-val y))
                       (equal (after x) (after y)))))
  :use (equal-of-from-cursor-when-equal-of-view
        (:instance zip-uniqueness (zip1 x) (zip2 y))
        (:instance zip-after-of-cursor-fix-becomes-to-omap-of-after
                   (cursor x))
        (:instance zip-after-of-cursor-fix-becomes-to-omap-of-after
                   (cursor y)))
  :enable (from-cursor
           entryp
           break-abstraction))

(defruled cursor-extensionality-no-backchain-limit
  (implies (and (cursorp x)
                (cursorp y)
                (cursor-equiv x$ (double-rewrite x))
                (cursor-equiv y$ (double-rewrite y)))
           (equal (equal x y)
                  (and (equal (entryp x$) (entryp y$))
                       (equal (before x$) (before y$))
                       (equal (entry-key x$) (entry-key y$))
                       (equal (entry-val x$) (entry-val y$))
                       (equal (after x$) (after y$)))))
  :use equal-of-cursors)

(defruled cursor-extensionality
  (implies (and (cursorp x)
                (cursorp y)
                (cursor-equiv x$ (double-rewrite x))
                (cursor-equiv y$ (double-rewrite y)))
           (equal (equal x y)
                  (and (equal (entryp x$) (entryp y$))
                       (equal (before x$) (before y$))
                       (equal (entry-key x$) (entry-key y$))
                       (equal (entry-val x$) (entry-val y$))
                       (equal (after x$) (after y$)))))
  :parents (cursor)
  :short "A @(see cursor) is determined by what is before it, what it is at,
          and what is after it."
  :long
  (xdoc::topstring
   (xdoc::p
     "Two cursors are equal exactly when they agree on @(tsee entryp), @(tsee
      before), @(tsee entry-key), @(tsee entry-val), and @(tsee after).
      Equalities between cursors are proved by enabling the
      @('cursor-extensionality') rule.")
   (xdoc::p
     "Two cursors at entries are also equal exactly when they agree on @(tsee
      from-cursor) and @(tsee entry-key). This is the
      @('cursor-extensionality-when-entryp') rule."))
  :rule-classes ((:rewrite :backchain-limit-lst (1 1 nil nil)))
  :by cursor-extensionality-no-backchain-limit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl equal-of-cursors-when-entryp
  (implies (and (cursorp x)
                (cursorp y)
                (entryp x)
                (entryp y))
           (equal (equal x y)
                  (and (equal (from-cursor x) (from-cursor y))
                       (equal (entry-key x) (entry-key y)))))
  :use (:instance zip-uniqueness-when-same-key (zip1 x) (zip2 y))
  :enable (from-cursor
           entry-key
           entryp
           break-abstraction))

(defruled cursor-extensionality-when-entryp-no-backchain-limit
  (implies (and (cursorp x)
                (cursorp y)
                (cursor-equiv x$ (double-rewrite x))
                (cursor-equiv y$ (double-rewrite y))
                (entryp x$)
                (entryp y$))
           (equal (equal x y)
                  (and (equal (from-cursor x$) (from-cursor y$))
                       (equal (entry-key x$) (entry-key y$)))))
  :use equal-of-cursors-when-entryp)

(defruled cursor-extensionality-when-entryp
  (implies (and (cursorp x)
                (cursorp y)
                (cursor-equiv x$ (double-rewrite x))
                (cursor-equiv y$ (double-rewrite y))
                (entryp x$)
                (entryp y$))
           (equal (equal x y)
                  (and (equal (from-cursor x$) (from-cursor y$))
                       (equal (entry-key x$) (entry-key y$)))))
  :rule-classes ((:rewrite :backchain-limit-lst (1 1 nil nil 1 1)))
  :by cursor-extensionality-when-entryp-no-backchain-limit)
