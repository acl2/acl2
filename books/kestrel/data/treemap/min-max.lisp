; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)

(include-book "kestrel/data/treeset/min-max-defs" :dir :system)

(include-book "internal/min-max-defs")
(include-book "map-defs")
(include-book "keys-defs")
(include-book "lookup-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/keys"))
(local (include-book "internal/min-max"))
(local (include-book "map"))
(local (include-book "keys"))
(local (include-book "lookup"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define min-key ((map mapp))
  :parents (min)
  :short "The minimum key of a @(see treemap) (with respect to @(tsee <<))."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(\\log(n))$).")
   (xdoc::p
     "This function is enabled by default."))
  :guard (not (emptyp map))
  (mbe :logic (treeset::min (keys map))
       :exec (car (tree-leftmost map)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* keys
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define min-val ((map mapp))
  :parents (min)
  :short "The value associated with the @(tsee min-key) under a
          @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(\\log(n))$).")
   (xdoc::p
     "This function is enabled by default."))
  :guard (not (emptyp map))
  (mbe :logic (lookup (treeset::min (keys map)) map)
       :exec (cdr (tree-leftmost map)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* keys
                                            lookup
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define min ((map mapp))
  :parents (treemap)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max-key ((map mapp))
  :parents (max)
  :short "The maximum key of a @(see treemap) (with respect to @(tsee <<))."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(\\log(n))$).")
   (xdoc::p
     "This function is enabled by default."))
  :guard (not (emptyp map))
  (mbe :logic (treeset::max (keys map))
       :exec (car (tree-rightmost map)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* keys
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max-val ((map mapp))
  :parents (max)
  :short "The value associated with the @(tsee max-key) under a
          @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(\\log(n))$).")
   (xdoc::p
     "This function is enabled by default."))
  :guard (not (emptyp map))
  (mbe :logic (lookup (treeset::max (keys map)) map)
       :exec (cdr (tree-rightmost map)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* keys
                                            lookup
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max ((map mapp))
  :parents (treemap)
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
