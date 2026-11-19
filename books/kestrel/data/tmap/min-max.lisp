; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/omaps/defs" :dir :system)

(include-book "kestrel/data/tset/min-max-defs" :dir :system)

(include-book "internal/min-max-defs")
(include-book "map-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "to-omap-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/min-max" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/keys"))
(local (include-book "internal/min-max"))
(local (include-book "map"))
(local (include-book "keys"))
(local (include-book "lookup"))
(local (include-book "to-omap"))

(local (include-book "std/omaps/assoc" :dir :system))
(local (include-book "kestrel/data/utilities/omap" :dir :system))
(local (include-book "kestrel/data/tset/to-oset" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define min-key ((map mapp))
  :parents (min)
  :short "The minimum key of a @(see tmap) (with respect to @(tsee <<))."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(\\log(n))$).")
   (xdoc::p
     "This function is enabled by default."))
  :guard (not (emptyp map))
  (mbe :logic (tset::min (keys map))
       :exec (car (tree-leftmost map)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* keys
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define min-val ((map mapp))
  :parents (min)
  :short "The value associated with the @(tsee min-key) under a
          @(see tmap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(\\log(n))$).")
   (xdoc::p
     "This function is enabled by default."))
  :guard (not (emptyp map))
  (mbe :logic (lookup (tset::min (keys map)) map)
       :exec (cdr (tree-leftmost map)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* keys
                                            lookup
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define min ((map mapp))
  :parents (tmap)
  :short "The @(tsee min-key) and @(tsee min-val)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(\\log(n))$).")
   (xdoc::p
     "This function is enabled by default."))
  :guard (not (emptyp map))
  :returns (mv key val)
  (mbe :logic (mv (min-key map) (min-val map))
       :exec (let ((key+val (tree-leftmost map)))
               (mv (car key+val) (cdr key+val))))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* keys
                                            lookup
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule head-key-of-to-omap
  (equal (mv-nth 0 (omap::head (to-omap map)))
         (tset::min (keys map)))
  :enable data::head-key-becomes-head-of-keys)

(add-to-ruleset from-omap-theory '(head-key-of-to-omap))

(defrule head-value-of-to-omap
  (equal (mv-nth 1 (omap::head (to-omap map)))
         (lookup (tset::min (keys map)) map))
  :use (:instance omap::assoc-of-head-key (map (to-omap map))))

(add-to-ruleset from-omap-theory '(head-value-of-to-omap))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max-key ((map mapp))
  :parents (max)
  :short "The maximum key of a @(see tmap) (with respect to @(tsee <<))."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(\\log(n))$).")
   (xdoc::p
     "This function is enabled by default."))
  :guard (not (emptyp map))
  (mbe :logic (tset::max (keys map))
       :exec (car (tree-rightmost map)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* keys
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max-val ((map mapp))
  :parents (max)
  :short "The value associated with the @(tsee max-key) under a
          @(see tmap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(\\log(n))$).")
   (xdoc::p
     "This function is enabled by default."))
  :guard (not (emptyp map))
  (mbe :logic (lookup (tset::max (keys map)) map)
       :exec (cdr (tree-rightmost map)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* keys
                                            lookup
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max ((map mapp))
  :parents (tmap)
  :short "The @(tsee max-key) and @(tsee max-val)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(\\log(n))$).")
   (xdoc::p
     "This function is enabled by default."))
  :guard (not (emptyp map))
  :returns (mv key val)
  (mbe :logic (mv (max-key map) (max-val map))
       :exec (let ((key+val (tree-rightmost map)))
               (mv (car key+val) (cdr key+val))))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* keys
                                            lookup
                                            break-abstraction))))
