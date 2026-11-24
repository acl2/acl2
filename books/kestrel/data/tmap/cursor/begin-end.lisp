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
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/in" :dir :system))

(local (include-book "../internal/tree"))
(local (include-book "../map"))
(local (include-book "../keys"))
(local (include-book "../lookup"))
(local (include-book "../extensionality"))
(local (include-book "cursor"))
(local (include-book "entry"))
(local (include-book "before-after"))
(local (include-book "internal/before-after"))
(local (include-book "from-cursor"))
(local (include-book "extensionality"))

(local (include-book "internal/zip-step"))
(local (include-book "internal/zip-step-side"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define beginp ((cursor cursorp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (cursor)
  :short "Check whether a @(see cursor) is at the hole before every entry."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(\\log(n))$).")
  (mbe :logic (and (not (entryp cursor))
                   (emptyp (before cursor)))
       :exec (zip-at-begin-p (cursor-fix cursor)))
  :inline t
  :guard-hints
  (("Goal" :in-theory (enable* entryp
                               emptyp-of-before-becomes-not-consp
                               zip-at-begin-p-becomes-not-consp-of-zip-before
                               break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define endp ((cursor cursorp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (cursor)
  :short "Check whether a @(see cursor) is at the hole after every entry."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(\\log(n))$).")
  (mbe :logic (and (not (entryp cursor))
                   (emptyp (after cursor)))
       :exec (zip-at-end-p (cursor-fix cursor)))
  :inline t
  :guard-hints
  (("Goal" :in-theory (enable* entryp
                               emptyp-of-after-becomes-not-consp
                               zip-at-end-p-becomes-not-consp-of-zip-after
                               break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule beginp-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (beginp cursor0)
                  (beginp cursor1)))
  :rule-classes :congruence
  :enable beginp)

(defrule endp-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (endp cursor0)
                  (endp cursor1)))
  :rule-classes :congruence
  :enable endp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled not-entryp-when-beginp
  (implies (beginp cursor)
           (not (entryp cursor)))
  :enable beginp)

(defrule not-entryp-when-beginp-forward-chaining
  (implies (beginp cursor)
           (not (entryp cursor)))
  :rule-classes :forward-chaining
  :by not-entryp-when-beginp)

(defruled not-entryp-when-endp
  (implies (endp cursor)
           (not (entryp cursor)))
  :enable endp)

(defrule not-entryp-when-endp-forward-chaining
  (implies (endp cursor)
           (not (entryp cursor)))
  :rule-classes :forward-chaining
  :by not-entryp-when-endp)

(defruled not-beginp-when-entryp
  (implies (entryp cursor)
           (not (beginp cursor))))

(defrule not-beginp-when-entryp-forward-chaining
  (implies (entryp cursor)
           (not (beginp cursor)))
  :rule-classes :forward-chaining
  :by not-beginp-when-entryp)

(defruled not-endp-when-entryp
  (implies (entryp cursor)
           (not (endp cursor))))

(defrule not-endp-when-entryp-forward-chaining
  (implies (entryp cursor)
           (not (endp cursor)))
  :rule-classes :forward-chaining
  :by not-endp-when-entryp)

;;;;;;;;;;;;;;;;;;;;

(defruled before-when-beginp
  (implies (beginp cursor)
           (equal (before cursor)
                  (empty)))
  :enable (beginp
           emptyp-alt-definition))

(defruled emptyp-of-before-when-beginp
  (implies (beginp cursor)
           (emptyp (before cursor)))
  :enable beginp)

(defrule emptyp-of-before-when-beginp-forward-chaining
  (implies (beginp cursor)
           (emptyp (before cursor)))
  :rule-classes :forward-chaining
  :by emptyp-of-before-when-beginp)

(defruled after-when-endp
  (implies (endp cursor)
           (equal (after cursor)
                  (empty)))
  :enable (endp
           emptyp-alt-definition))

(defruled emptyp-of-after-when-endp
  (implies (endp cursor)
           (emptyp (after cursor)))
  :enable endp)

(defrule emptyp-of-after-when-endp-forward-chaining
  (implies (endp cursor)
           (emptyp (after cursor)))
  :rule-classes :forward-chaining
  :by emptyp-of-after-when-endp)

(defruled after-when-beginp
  (implies (beginp cursor)
           (equal (after cursor)
                  (from-cursor cursor)))
  :enable (extensionality
           lookup-of-from-cursor-becomes-lookup-of-before-or-entry-val-or-after))

(defrule after-when-beginp-cheap
  (implies (beginp cursor)
           (equal (after cursor)
                  (from-cursor cursor)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by after-when-beginp)

(defruled before-when-endp
  (implies (endp cursor)
           (equal (before cursor)
                  (from-cursor cursor)))
  :enable (extensionality
           lookup-of-from-cursor-becomes-lookup-of-before-or-entry-val-or-after))

(defrule before-when-endp-cheap
  (implies (endp cursor)
           (equal (before cursor)
                  (from-cursor cursor)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by before-when-endp)

;;;;;;;;;;;;;;;;;;;;

(defruled not-emptyp-of-before-when-not-beginp-and-not-entryp
  (implies (and (not (beginp cursor))
                (not (entryp cursor)))
           (not (emptyp (before cursor))))
  :enable beginp)

(defrule not-emptyp-of-before-when-not-beginp-and-not-entryp-forward-chaining
  (implies (and (not (beginp cursor))
                (not (entryp cursor)))
           (not (emptyp (before cursor))))
  :rule-classes :forward-chaining
  :by not-emptyp-of-before-when-not-beginp-and-not-entryp)

(defruled not-emptyp-of-after-when-not-endp-and-not-entryp
  (implies (and (not (endp cursor))
                (not (entryp cursor)))
           (not (emptyp (after cursor))))
  :enable endp)

(defrule not-emptyp-of-after-when-not-endp-and-not-entryp-forward-chaining
  (implies (and (not (endp cursor))
                (not (entryp cursor)))
           (not (emptyp (after cursor))))
  :rule-classes :forward-chaining
  :by not-emptyp-of-after-when-not-endp-and-not-entryp)

;;;;;;;;;;;;;;;;;;;;

(defruled emptyp-of-from-cursor-when-beginp-and-endp
  (implies (and (beginp cursor)
                (endp cursor))
           (emptyp (from-cursor cursor)))
  :enable (endp
           after-when-beginp))

(defrule emptyp-of-from-cursor-when-beginp-and-endp-forward-chaining
  (implies (and (beginp cursor)
                (endp cursor))
           (emptyp (from-cursor cursor)))
  :rule-classes :forward-chaining
  :by emptyp-of-from-cursor-when-beginp-and-endp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule beginp-of-begin
  (beginp (begin map))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((begin map))))
  :enable (beginp
           entryp
           begin
           emptyp-of-before-becomes-not-consp
           break-abstraction))

(defrule endp-of-end
  (endp (end map))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((end map))))
  :enable (endp
           entryp
           end
           emptyp-of-after-becomes-not-consp
           break-abstraction))

(defrule not-entryp-of-begin
  (not (entryp (begin map))))

(defrule not-entryp-of-end
  (not (entryp (end map))))

(defrule from-cursor-of-begin
  (equal (from-cursor (begin map))
         (fix map))
  :enable (from-cursor
           begin
           break-abstraction))

(defrule from-cursor-of-end
  (equal (from-cursor (end map))
         (fix map))
  :enable (from-cursor
           end
           break-abstraction))

(defrule before-of-begin
  (equal (before (begin map))
         (empty))
  :enable before-when-beginp)

(defrule after-of-end
  (equal (after (end map))
         (empty))
  :enable after-when-endp)

(defrule after-of-begin
  (equal (after (begin map))
         (fix map)))

(defrule before-of-end
  (equal (before (end map))
         (fix map)))

(defrule endp-of-begin
  (equal (endp (begin map))
         (emptyp map))
  :enable endp)

(defrule beginp-of-end
  (equal (beginp (end map))
         (emptyp map))
  :enable beginp)

(defrule equal-of-begin-and-end
  (equal (equal (begin x) (end y))
         (and (emptyp x)
              (emptyp y)))
  :enable (cursor-extensionality
           emptyp-alt-definition))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled beginp-becomes-equal-of-begin
  (equal (beginp cursor)
         (equal (cursor-fix cursor)
                (begin (from-cursor cursor))))
  :enable (cursor-extensionality
           beginp
           emptyp-alt-definition)
  :use after-when-beginp)

(defruled endp-becomes-equal-of-end
  (equal (endp cursor)
         (equal (cursor-fix cursor)
                (end (from-cursor cursor))))
  :enable (cursor-extensionality
           endp
           emptyp-alt-definition)
  :use before-when-endp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy begin-end-extra-rules
  '(not-entryp-when-beginp
    not-entryp-when-endp
    not-beginp-when-entryp
    not-endp-when-entryp
    before-when-beginp
    emptyp-of-before-when-beginp
    after-when-endp
    emptyp-of-after-when-endp
    after-when-beginp
    before-when-endp
    not-emptyp-of-before-when-not-beginp-and-not-entryp
    not-emptyp-of-after-when-not-endp-and-not-entryp
    emptyp-of-from-cursor-when-beginp-and-endp))
