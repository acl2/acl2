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
(include-book "std/osets/defs" :dir :system)

(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/compare-defs" :dir :system)

(include-book "../../internal/tree-defs")
(include-book "../../internal/bst-defs")
(include-book "../../internal/in-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")
(include-book "zip-move-defs")
(include-book "zip-side-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/oset" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (include-book "../../internal/tree"))
(local (include-book "../../internal/bst"))
(local (include-book "../../internal/in"))
(local (include-book "../../internal/in-order"))
(local (include-book "zip-frame"))
(local (include-book "zipper"))
(local (include-book "zip-move"))
(local (include-book "zip-side"))
(local (include-book "zip-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (xdoc::set-default-parents zipper))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-seek
  (x
   (zip zipp))
  :type-prescription :none
  :returns (zip$ zipp)
  :short "Move the focus to a value within it, or to the hole where the value
          would be."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is the search of @(tsee tree-search-in), which assumes that the
      focus is a search tree.")
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth descended, and so
      @($O(\\log(n))$) over a @(see tset)."))
  (if (tree-empty-p (zip->focus zip))
      (zip-fix zip)
    (mv-let (equalp ltp)
            (data::compare-<< x (zip-value zip))
      (cond (equalp (zip-fix zip))
            (ltp (zip-seek x (zip-descend-left zip)))
            (t (zip-seek x (zip-descend-right zip))))))
  :measure (acl2-count (zip->focus zip)))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-seek-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-seek x zip0)
                  (zip-seek x zip1)))
  :rule-classes :congruence
  :expand ((zip-seek x zip0)
           (zip-seek x zip1)))

(defrule zip-plug-of-zip-seek
  (equal (zip-plug (zip-seek x zip))
         (zip-plug zip))
  :induct t
  :enable zip-seek)

(defrule tree-empty-p-of-focus-of-zip-seek
  (equal (tree-empty-p (zip->focus (zip-seek x zip)))
         (not (tree-search-in x (zip->focus zip))))
  :induct (zip-seek x zip)
  :enable (zip-seek
           tree-search-in
           zip-value))

(defrule zip-value-of-zip-seek
  (implies (tree-search-in x (zip->focus zip))
           (equal (zip-value (zip-seek x zip))
                  x))
  :induct (zip-seek x zip)
  :enable (zip-seek
           tree-search-in
           zip-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-zip-seek
  ((x acl2-numberp)
   (zip zipp))
  :type-prescription :none
  :guard (tree-all-acl2-numberp (zip->focus zip))
  (mbe :logic (zip-seek x zip)
       :exec (if (tree-empty-p (zip->focus zip))
                 zip
               (mv-let (equalp ltp)
                       (data::acl2-number-compare-<< x (zip-value zip))
                 (cond (equalp zip)
                       (ltp (acl2-number-zip-seek x (zip-descend-left zip)))
                       (t (acl2-number-zip-seek x (zip-descend-right zip)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable zip-seek
                                           acl2-number-zip-seek
                                           zip-value
                                           tree-all-acl2-numberp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-zip-seek
  ((x symbolp)
   (zip zipp))
  :type-prescription :none
  :guard (tree-all-symbolp (zip->focus zip))
  (mbe :logic (zip-seek x zip)
       :exec (if (tree-empty-p (zip->focus zip))
                 zip
               (mv-let (equalp ltp)
                       (data::symbol-compare-<< x (zip-value zip))
                 (cond (equalp zip)
                       (ltp (symbol-zip-seek x (zip-descend-left zip)))
                       (t (symbol-zip-seek x (zip-descend-right zip)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable zip-seek
                                           symbol-zip-seek
                                           zip-value
                                           tree-all-symbolp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-zip-seek
  ((x eqlablep)
   (zip zipp))
  :type-prescription :none
  :guard (tree-all-eqlablep (zip->focus zip))
  (mbe :logic (zip-seek x zip)
       :exec (if (tree-empty-p (zip->focus zip))
                 zip
               (mv-let (equalp ltp)
                       (data::eqlable-compare-<< x (zip-value zip))
                 (cond (equalp zip)
                       (ltp (eqlable-zip-seek x (zip-descend-left zip)))
                       (t (eqlable-zip-seek x (zip-descend-right zip)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable zip-seek
                                           eqlable-zip-seek
                                           zip-value
                                           tree-all-eqlablep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A zipper brackets a value when the nearest value before the focus subtree
;; is below it, and the nearest value after is above it. The search keeps the
;; sought value bracketed.

(local
  (define zip-brackets-p
    (x
     (zip zipp))
    :type-prescription :none
    :returns (yes/no booleanp :rule-classes :type-prescription)
    :verify-guards nil
    (let ((before (zip-path-before (zip->path zip)))
          (after (zip-path-after (zip->path zip))))
      (and (or (not (consp before))
               (<< (car (last before)) x))
           (or (not (consp after))
               (<< x (car after)))))))

(defrulel zip-brackets-p-of-zip-root
  (zip-brackets-p x (zip-root tree))
  :enable zip-brackets-p)

(defrulel zip-brackets-p-of-zip-seek
  (implies (zip-brackets-p x zip)
           (zip-brackets-p x (zip-seek x zip)))
  :induct (zip-seek x zip)
  :enable (zip-seek
           zip-brackets-p
           zip-value
           data::<<-rules))

(defruledl <<-of-car-of-last-of-zip-before-when-zip-brackets-p
  (implies (and (zip-brackets-p x zip)
                (tree-empty-p (zip->focus zip))
                (consp (zip-before zip)))
           (<< (car (last (zip-before zip))) x))
  :enable (zip-brackets-p
           zip-before))

(defruledl <<-of-arg1-and-car-of-zip-after-when-zip-brackets-p
  (implies (and (zip-brackets-p x zip)
                (tree-empty-p (zip->focus zip))
                (consp (zip-after zip)))
           (<< x (car (zip-after zip))))
  :enable (zip-brackets-p
           zip-after))

;;;;;;;;;;;;;;;;;;;;

;; So at the hole of an unsuccessful search, the values before are those below
;; the sought value, and the values after are those above it.

(defruledl tree-in-of-zip-plug-when-tree-empty-p-of-focus
  (implies (tree-empty-p (zip->focus zip))
           (equal (tree-in y (zip-plug zip))
                  (or (and (member-equal y (zip-before zip)) t)
                      (and (member-equal y (zip-after zip)) t))))
  :enable (tree-in-becomes-member-equal-of-tree-in-order
           tree-in-order-of-zip-plug-split-at-cursor)
  :disable member-equal-of-tree-in-order-under-iff)

(defruledl in-of-zip-oset-before-of-zip-seek-when-not-tree-search-in
  (implies (and (bstp (zip-plug (zip-seek x zip)))
                (not (tree-search-in x (zip->focus zip)))
                (zip-brackets-p x zip))
           (equal (set::in y (zip-oset-before (zip-seek x zip)))
                  (and (tree-in y (zip-plug (zip-seek x zip)))
                       (<< y x))))
  :enable (tree-in-of-zip-plug-when-tree-empty-p-of-focus
           <<-of-car-of-last-of-zip-before-when-zip-brackets-p
           <<-of-arg1-and-car-of-zip-after-when-zip-brackets-p
           data::<<-when-member-equal-and-<<-of-car-of-last
           data::<<-when-member-equal-and-<<-of-arg1-and-car
           data::<<-rules
           acl2::consp-when-member-equal
           not-member-equal-of-zip-before-when-member-equal-of-zip-after)
  :disable zip-plug-of-zip-seek)

(defruledl in-of-zip-oset-after-of-zip-seek-when-not-tree-search-in
  (implies (and (bstp (zip-plug (zip-seek x zip)))
                (not (tree-search-in x (zip->focus zip)))
                (zip-brackets-p x zip))
           (equal (set::in y (zip-oset-after (zip-seek x zip)))
                  (and (tree-in y (zip-plug (zip-seek x zip)))
                       (<< x y))))
  :enable (tree-in-of-zip-plug-when-tree-empty-p-of-focus
           <<-of-car-of-last-of-zip-before-when-zip-brackets-p
           <<-of-arg1-and-car-of-zip-after-when-zip-brackets-p
           data::<<-when-member-equal-and-<<-of-car-of-last
           data::<<-when-member-equal-and-<<-of-arg1-and-car
           data::<<-rules
           acl2::consp-when-member-equal
           not-member-equal-of-zip-after-when-member-equal-of-zip-before)
  :disable zip-plug-of-zip-seek)

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-zip-oset-before-of-zip-seek-of-zip-root
  (implies (bstp tree)
           (equal (set::in y (zip-oset-before (zip-seek x (zip-root tree))))
                  (and (tree-in y tree)
                       (<< y x))))
  :cases ((tree-in x tree))
  :enable in-of-zip-oset-before-of-zip-seek-when-not-tree-search-in)

(defrule in-of-zip-oset-after-of-zip-seek-of-zip-root
  (implies (bstp tree)
           (equal (set::in y (zip-oset-after (zip-seek x (zip-root tree))))
                  (and (tree-in y tree)
                       (<< x y))))
  :cases ((tree-in x tree))
  :enable in-of-zip-oset-after-of-zip-seek-when-not-tree-search-in)
