; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TBAG")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/tset/in-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/map-defs" :dir :system)
(include-book "kestrel/data/tmap/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/lookup-defs" :dir :system)
(include-book "kestrel/data/tmap/update-defs" :dir :system)
(include-book "kestrel/data/tmap/delete-defs" :dir :system)

(include-book "bag-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/keys" :dir :system))
(local (include-book "kestrel/data/tmap/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/update" :dir :system))
(local (include-book "kestrel/data/tmap/delete" :dir :system))

(local (include-book "internal/map-values-all-posp"))
(local (include-book "bag"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define count (x (bag bagp))
  :type-prescription :none
  :returns (count natp
                  :rule-classes ((:rewrite) (:type-prescription))
                  :hints (("Goal" :in-theory (enable* break-abstraction))))
  :parents (tbag)
  :short "The number of occurrences of a value in a @(see tbag)."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(\\log(m))$), where @($m$) is the number of distinct
     elements of the bag.")
  ;; Reading 0 for an absent element loses nothing, since no element of a
  ;; @(see tbag) is bound to 0.
  (tmap::lookup x (fix bag) :default 0)
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule count-when-equiv-congruence
  (implies (equiv bag0 bag1)
           (equal (count x bag0)
                  (count x bag1)))
  :rule-classes :congruence
  :enable count)

(defruled count-when-emptyp
  (implies (emptyp bag)
           (equal (count x bag)
                  0))
  :enable (count
           emptyp))

(defrule count-when-emptyp-cheap
  (implies (emptyp bag)
           (equal (count x bag)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable count-when-emptyp)

(defruled not-emptyp-when-count-nonzero
  (implies (not (equal (count x bag) 0))
           (not (emptyp bag)))
  :use count-when-emptyp)

(defrule count-of-arg1-and-empty
  (equal (count x (empty))
         0)
  :enable count-when-emptyp)

;; Reading counts after binding an element to a positive value, or removing
;; it, in the underlying tmap.

(defruled count-of-tmap-update
  (implies (posp v)
           (equal (count y (tmap::update x v (fix bag)))
                  (if (equal y x)
                      v
                    (count y bag))))
  :enable (count
           break-abstraction))

(add-to-ruleset break-abstraction '(count-of-tmap-update))

(defruled count-of-tmap-delete
  (equal (count y (tmap::delete x (fix bag)))
         (if (equal y x)
             0
           (count y bag)))
  :enable (count
           break-abstraction))

(add-to-ruleset break-abstraction '(count-of-tmap-delete))

;; A value that is not a key of a bag's tree does not occur in the bag.

(defruled count-when-not-in-tree-key-set-of-fix
  (implies (not (tset::in x (tmap::tree-key-set (fix bag))))
           (equal (count x bag)
                  0))
  :enable (count
           break-abstraction
           tmap::lookup
           tmap::keys))

(add-to-ruleset break-abstraction '(count-when-not-in-tree-key-set-of-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in (x (bag bagp))
  :type-prescription :none
  :parents (tbag)
  :short "Check if a value occurs in a @(see tbag)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(m))$), where @($m$) is the number of
       distinct elements of the bag.")
    (xdoc::p
      "This is a convenient abbreviation, not the logical normal form used by
       this library. It is enabled, so @('(in x bag)') becomes @('(< 0 (count
       x bag))')."))
  (< 0 (count x bag))
  :enabled t
  :inline t)
