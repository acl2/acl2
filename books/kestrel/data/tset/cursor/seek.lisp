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
(include-book "../min-max-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")
(include-book "begin-end-defs")
(include-book "seek-min-max-defs")
(include-book "internal/zip-seek-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "../internal/tree"))
(local (include-book "../internal/in"))
(local (include-book "../set"))
(local (include-book "../in"))
(local (include-book "../min-max"))
(local (include-book "../insert"))
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
  :short "Construct a @(see cursor) at a value of a @(see tset), or at the
          hole where the value would be."
  :long
  (xdoc::topstring
    (xdoc::p
      "If the value is in the set, the cursor is at that entry. Otherwise, it
       is at the hole between the elements below the value and the elements
       above it. Either way, @(tsee before) is the elements below the value,
       and @(tsee after) is the elements above it.")
    (xdoc::p
      "Time complexity: @($O(\\log(n))$).")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(seek x set :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the set consists of elements
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro seek (x set &key (test 'equal))
  (declare (xargs :guard (member-eq test '(equal = eq eql))))
  (case test
    (equal `(seek$inline ,x ,set))
    (=     `(seek-=      ,x ,set))
    (eq    `(seek-eq     ,x ,set))
    (eql   `(seek-eql    ,x ,set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define seek$inline
  (x
   (set setp))
  :type-prescription :none
  :returns (cursor cursorp
                   :hints (("Goal" :in-theory (enable* cursorp
                                                       break-abstraction))))
  (zip-seek x (zip-root (fix set)))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction)))

  ///
  (add-macro-fn seek seek$inline))

;;;;;;;;;;;;;;;;;;;;

(defrule seek-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (seek x set0)
                  (seek x set1)))
  :rule-classes :congruence
  :enable seek)

(defruled cursor-fix-of-zip-seek-of-zip-root-of-fix
  (equal (cursor-fix (zip-seek x (zip-root (fix set))))
         (zip-seek x (zip-root (fix set))))
  :use cursorp-of-seek$inline
  :enable seek)

(add-to-ruleset break-abstraction '(cursor-fix-of-zip-seek-of-zip-root-of-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule from-cursor-of-seek
  (equal (from-cursor (seek x set))
         (fix set))
  :enable (from-cursor
           seek
           break-abstraction))

(defrule entryp-of-seek
  (equal (entryp (seek x set))
         (in x set))
  :enable (entryp
           seek
           in
           not
           break-abstraction))

(defrule entry-of-seek-when-in
  (implies (in x set)
           (equal (entry (seek x set))
                  x))
  :enable (entry
           seek
           in
           break-abstraction))

(defruled entry-of-seek
  (equal (entry (seek x set))
         (if (in x set)
             x
           nil))
  :enable entry-when-not-entryp)

(defrule in-of-before-of-seek
  (equal (in y (before (seek x set)))
         (and (in y set)
              (<< y x)))
  :enable (before
           seek
           in
           break-abstraction))

(defrule in-of-after-of-seek
  (equal (in y (after (seek x set)))
         (and (in y set)
              (<< x y)))
  :enable (after
           seek
           in
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-before-of-seek
  (equal (emptyp (before (seek x set)))
         (or (emptyp set)
             (not (<< (min set) x))))
  :use ((:instance in-of-min
                   (set (before (seek x set))))
        (:instance not-emptyp-when-in
                   (x (min set))
                   (set (before (seek x set)))))
  :enable <<-of-min-when-in-and-<<)

(defrule emptyp-of-after-of-seek
  (equal (emptyp (after (seek x set)))
         (or (emptyp set)
             (not (<< x (max set)))))
  :use ((:instance in-of-max
                   (set (after (seek x set))))
        (:instance not-emptyp-when-in
                   (x (max set))
                   (set (after (seek x set)))))
  :enable <<-of-arg1-and-max-when-in-and-<<)

;;;;;;;;;;;;;;;;;;;;

(defrule beginp-of-seek
  (equal (beginp (seek x set))
         (or (emptyp set)
             (<< x (min set))))
  :cases ((equal x (min set)))
  :enable (beginp
           not
           data::<<-rules))

(defrule endp-of-seek
  (equal (endp (seek x set))
         (or (emptyp set)
             (<< (max set) x)))
  :cases ((equal x (max set)))
  :enable (endp
           not
           data::<<-rules))

(defrule minp-of-seek
  (equal (minp (seek x set))
         (and (not (emptyp set))
              (equal x (min set))))
  :enable (minp
           data::<<-rules))

(defrule maxp-of-seek
  (equal (maxp (seek x set))
         (and (not (emptyp set))
              (equal x (max set))))
  :enable (maxp
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule seek-of-entry-and-from-cursor
  (implies (entryp cursor)
           (equal (seek (entry cursor) (from-cursor cursor))
                  (cursor-fix cursor)))
  :enable cursor-extensionality-when-entryp)

(defrule seek-of-min
  (equal (seek (min set) set)
         (seek-min set))
  :enable (cursor-extensionality
           extensionality
           entry-of-seek))

(defrule seek-of-max
  (equal (seek (max set) set)
         (seek-max set))
  :enable (cursor-extensionality
           extensionality
           entry-of-seek))

;;;;;;;;;;;;;;;;;;;;

(defruled seek-when-emptyp
  (implies (emptyp set)
           (equal (seek x set)
                  (begin set)))
  :enable (cursor-extensionality
           extensionality
           entry-of-seek))

(defrule seek-when-emptyp-cheap
  (implies (emptyp set)
           (equal (seek x set)
                  (begin set)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by seek-when-emptyp)

(defruled seek-when-<<-of-arg1-and-min
  (implies (<< x (min set))
           (equal (seek x set)
                  (begin set)))
  :enable (cursor-extensionality
           extensionality
           entry-of-seek
           <<-of-min-when-in-and-<<
           <<-when-in-and-<<-of-arg1-and-min
           data::<<-rules))

(defrule seek-when-<<-of-arg1-and-min-cheap
  (implies (<< x (min set))
           (equal (seek x set)
                  (begin set)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by seek-when-<<-of-arg1-and-min)

(defruled seek-when-<<-of-max-and-arg1
  (implies (<< (max set) x)
           (equal (seek x set)
                  (end set)))
  :enable (cursor-extensionality
           extensionality
           entry-of-seek
           <<-of-arg1-and-max-when-in-and-<<
           <<-when-in-and-<<-of-max
           data::<<-rules))

(defrule seek-when-<<-of-max-and-arg1-cheap
  (implies (<< (max set) x)
           (equal (seek x set)
                  (end set)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by seek-when-<<-of-max-and-arg1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define seek-=
  ((x acl2-numberp)
   (set acl2-number-setp))
  :type-prescription :none
  (mbe :logic (seek x set)
       :exec (acl2-number-zip-seek x (zip-root set)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-acl2-numberp
                                            seek))))

(define seek-eq
  ((x symbolp)
   (set symbol-setp))
  :type-prescription :none
  (mbe :logic (seek x set)
       :exec (symbol-zip-seek x (zip-root set)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-symbolp
                                            seek))))

(define seek-eql
  ((x eqlablep)
   (set eqlable-setp))
  :type-prescription :none
  (mbe :logic (seek x set)
       :exec (eqlable-zip-seek x (zip-root set)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-eqlablep
                                            seek))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy seek-extra-rules
  '(entry-of-seek
    seek-when-emptyp
    seek-when-<<-of-arg1-and-min
    seek-when-<<-of-max-and-arg1))
