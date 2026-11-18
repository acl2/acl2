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

(include-book "../map-defs")
(include-book "kestrel/data/tset/in-defs" :dir :system)
(include-book "../keys-defs")
(include-book "../lookup-defs")
(include-book "../min-max-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")
(include-book "begin-end-defs")
(include-book "seek-min-max-defs")
(include-book "internal/zip-seek-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/min-max" :dir :system))

(local (include-book "kestrel/data/utilities/omap" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "../internal/tree"))
(local (include-book "../internal/keys"))
(local (include-book "../internal/lookup"))
(local (include-book "../map"))
(local (include-book "../keys"))
(local (include-book "../lookup"))
(local (include-book "../update"))
(local (include-book "../min-max"))
(local (include-book "../delete"))
(local (include-book "../extensionality"))
(local (include-book "cursor"))
(local (include-book "entry"))
(local (include-book "before-after"))
(local (include-book "from-cursor"))
(local (include-book "extensionality"))
(local (include-book "begin-end"))
(local (include-book "seek-min-max"))
(local (include-book "internal/zipper"))
(local (include-book "internal/zip-seek"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc seek
  :parents (cursor)
  :short "Construct a @(see cursor) at a key of a @(see tmap), or at the hole
          where the key would be."
  :long
  (xdoc::topstring
    (xdoc::p
      "If the key is in the map, the cursor is at that entry. Otherwise, it is
       at the hole between the entries with keys below the key and the entries
       with keys above it. Either way, @(tsee before) is the entries below the
       key, and @(tsee after) is the entries above it.")
    (xdoc::p
      "Time complexity: @($O(\\log(n))$).")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(seek x map :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the keys of the map are
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro seek (x map &key (test 'equal))
  (declare (xargs :guard (member-eq test '(equal = eq eql))))
  (case test
    (equal `(seek$inline ,x ,map))
    (=     `(seek-=      ,x ,map))
    (eq    `(seek-eq     ,x ,map))
    (eql   `(seek-eql    ,x ,map))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define seek$inline
  (x
   (map mapp))
  :returns (cursor cursorp
                   :hints (("Goal" :in-theory (enable* cursorp
                                                       break-abstraction))))
  (zip-seek x (zip-root (fix map)))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction)))

  ///
  (add-macro-fn seek seek$inline))

;;;;;;;;;;;;;;;;;;;;

(defrule seek-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (seek x map0)
                  (seek x map1)))
  :rule-classes :congruence
  :enable seek)

(defruled cursor-fix-of-zip-seek-of-zip-root-of-fix
  (equal (cursor-fix (zip-seek x (zip-root (fix map))))
         (zip-seek x (zip-root (fix map))))
  :use cursorp-of-seek$inline
  :enable seek)

(add-to-ruleset break-abstraction '(cursor-fix-of-zip-seek-of-zip-root-of-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule from-cursor-of-seek
  (equal (from-cursor (seek x map))
         (fix map))
  :enable (from-cursor
           seek
           break-abstraction))

(defrule entryp-of-seek
  (equal (entryp (seek x map))
         (tset::in x (keys map)))
  :enable (entryp
           seek
           keys
           not
           break-abstraction))

(defrule entry-key-of-seek-when-in-of-keys
  (implies (tset::in x (keys map))
           (equal (entry-key (seek x map))
                  x))
  :enable (entry-key
           seek
           keys
           break-abstraction))

(defruled entry-key-of-seek
  (equal (entry-key (seek x map))
         (if (tset::in x (keys map))
             x
           nil))
  :enable entry-key-when-not-entryp)

(defrule entry-val-of-seek
  (equal (entry-val (seek x map))
         (lookup x map))
  :cases ((tset::in x (keys map)))
  :use (:instance lookup-of-entry-key-and-from-cursor
                  (cursor (seek x map))
                  (default nil))
  :enable entry-val-when-not-entryp
  :disable lookup-of-entry-key-and-from-cursor)

(defrule in-of-keys-of-before-of-seek
  (equal (tset::in y (keys (before (seek x map))))
         (and (tset::in y (keys map))
              (<< y x)))
  :enable (before
           seek
           keys
           omap::in-of-keys-to-assoc
           break-abstraction))

(defrule in-of-keys-of-after-of-seek
  (equal (tset::in y (keys (after (seek x map))))
         (and (tset::in y (keys map))
              (<< x y)))
  :enable (after
           seek
           keys
           omap::in-of-keys-to-assoc
           break-abstraction))

(defrule lookup-of-before-of-seek
  (equal (lookup y (before (seek x map)) :default default)
         (if (<< y x)
             (lookup y map :default default)
           default))
  :enable (before
           seek
           lookup
           keys
           break-abstraction))

(defrule lookup-of-after-of-seek
  (equal (lookup y (after (seek x map)) :default default)
         (if (<< x y)
             (lookup y map :default default)
           default))
  :enable (after
           seek
           lookup
           keys
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-before-of-seek
  (equal (emptyp (before (seek x map)))
         (or (emptyp map)
             (not (<< (min-key map) x))))
  :use ((:instance tset::in-of-min
                   (set (keys (before (seek x map)))))
        (:instance tset::not-emptyp-when-in
                   (x (min-key map))
                   (set (keys (before (seek x map))))))
  :enable tset::<<-of-min-when-in-and-<<)

(defrule emptyp-of-after-of-seek
  (equal (emptyp (after (seek x map)))
         (or (emptyp map)
             (not (<< x (max-key map)))))
  :use ((:instance tset::in-of-max
                   (set (keys (after (seek x map)))))
        (:instance tset::not-emptyp-when-in
                   (x (max-key map))
                   (set (keys (after (seek x map))))))
  :enable tset::<<-of-arg1-and-max-when-in-and-<<)

;;;;;;;;;;;;;;;;;;;;

(defrule beginp-of-seek
  (equal (beginp (seek x map))
         (or (emptyp map)
             (<< x (min-key map))))
  :cases ((equal x (min-key map)))
  :enable (beginp
           not
           data::<<-rules))

(defrule endp-of-seek
  (equal (endp (seek x map))
         (or (emptyp map)
             (<< (max-key map) x)))
  :cases ((equal x (max-key map)))
  :enable (endp
           not
           data::<<-rules))

(defrule minp-of-seek
  (equal (minp (seek x map))
         (and (not (emptyp map))
              (equal x (min-key map))))
  :enable (minp
           data::<<-rules))

(defrule maxp-of-seek
  (equal (maxp (seek x map))
         (and (not (emptyp map))
              (equal x (max-key map))))
  :enable (maxp
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule seek-of-entry-key-and-from-cursor
  (implies (entryp cursor)
           (equal (seek (entry-key cursor) (from-cursor cursor))
                  (cursor-fix cursor)))
  :enable cursor-extensionality-when-entryp)

(defrule seek-of-min-key
  (equal (seek (min-key map) map)
         (seek-min map))
  :enable (cursor-extensionality
           extensionality
           entry-key-of-seek))

(defrule seek-of-max-key
  (equal (seek (max-key map) map)
         (seek-max map))
  :enable (cursor-extensionality
           extensionality
           entry-key-of-seek))

;;;;;;;;;;;;;;;;;;;;

(defruled seek-when-emptyp
  (implies (emptyp map)
           (equal (seek x map)
                  (begin map)))
  :enable (cursor-extensionality
           extensionality
           entry-key-of-seek))

(defrule seek-when-emptyp-cheap
  (implies (emptyp map)
           (equal (seek x map)
                  (begin map)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by seek-when-emptyp)

(defruled seek-when-<<-of-arg1-and-min-key
  (implies (<< x (min-key map))
           (equal (seek x map)
                  (begin map)))
  :enable (cursor-extensionality
           extensionality
           entry-key-of-seek
           tset::<<-of-min-when-in-and-<<
           tset::<<-when-in-and-<<-of-arg1-and-min
           data::<<-rules))

(defrule seek-when-<<-of-arg1-and-min-key-cheap
  (implies (<< x (min-key map))
           (equal (seek x map)
                  (begin map)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by seek-when-<<-of-arg1-and-min-key)

(defruled seek-when-<<-of-max-key-and-arg1
  (implies (<< (max-key map) x)
           (equal (seek x map)
                  (end map)))
  :enable (cursor-extensionality
           extensionality
           entry-key-of-seek
           tset::<<-of-arg1-and-max-when-in-and-<<
           tset::<<-when-in-and-<<-of-max
           data::<<-rules))

(defrule seek-when-<<-of-max-key-and-arg1-cheap
  (implies (<< (max-key map) x)
           (equal (seek x map)
                  (end map)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by seek-when-<<-of-max-key-and-arg1)

;;;;;;;;;;;;;;;;;;;;

;; After a search, the key is above every entry before the cursor and below
;; every entry after it.

(defrule <<-of-max-of-keys-of-before-of-seek
  (implies (not (emptyp (before (seek x map))))
           (<< (tset::max (keys (before (seek x map)))) x))
  :use (:instance tset::in-of-max
                  (set (keys (before (seek x map)))))
  :disable tset::in-of-max)

(defrule <<-of-arg1-and-min-of-keys-of-after-of-seek
  (implies (not (emptyp (after (seek x map))))
           (<< x (tset::min (keys (after (seek x map))))))
  :use (:instance tset::in-of-min
                  (set (keys (after (seek x map)))))
  :disable tset::in-of-min)

;; Conversely, a hole is where a search for any such key ends.

(defruled seek-of-from-cursor-when-not-entryp
  (implies (and (not (entryp cursor))
                (or (emptyp (before cursor))
                    (<< (max-key (before cursor)) x))
                (or (emptyp (after cursor))
                    (<< x (min-key (after cursor)))))
           (equal (seek x (from-cursor cursor))
                  (cursor-fix cursor)))
  :enable (cursor-extensionality
           extensionality
           entry-key-of-seek
           in-of-keys-of-from-cursor-becomes-in-of-keys-of-before-or-entry-key-or-after
           lookup-of-from-cursor-becomes-lookup-of-before-or-entry-val-or-after
           tset::<<-when-in-and-<<-of-max
           tset::<<-when-in-and-<<-of-arg1-and-min
           data::<<-rules))

;; The hypotheses are checked without rewriting, so they are stated on the key
;; sets, as they appear once max-key and min-key have opened.

(defrule seek-of-from-cursor-when-not-entryp-cheap
  (implies (and (not (entryp cursor))
                (or (emptyp (before cursor))
                    (<< (tset::max (keys (before cursor))) x))
                (or (emptyp (after cursor))
                    (<< x (tset::min (keys (after cursor))))))
           (equal (seek x (from-cursor cursor))
                  (cursor-fix cursor)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 0)))
  :enable seek-of-from-cursor-when-not-entryp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define seek-=
  ((x acl2-numberp)
   (map acl2-number-mapp))
  (mbe :logic (seek x map)
       :exec (acl2-number-zip-seek x (zip-root map)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            map-keys-acl2-numberp
                                            keys
                                            seek))))

(define seek-eq
  ((x symbolp)
   (map symbol-mapp))
  (mbe :logic (seek x map)
       :exec (symbol-zip-seek x (zip-root map)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            map-keys-symbolp
                                            keys
                                            seek))))

(define seek-eql
  ((x eqlablep)
   (map eqlable-mapp))
  (mbe :logic (seek x map)
       :exec (eqlable-zip-seek x (zip-root map)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            map-keys-eqlablep
                                            keys
                                            seek))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy seek-extra-rules
  '(entry-key-of-seek
    seek-when-emptyp
    seek-when-<<-of-arg1-and-min-key
    seek-when-<<-of-max-key-and-arg1
    seek-of-from-cursor-when-not-entryp))
