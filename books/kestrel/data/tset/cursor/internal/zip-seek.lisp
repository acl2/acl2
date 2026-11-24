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
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/utilities/oset" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
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

;; The search, taking the focus and the path apart. These are the forms to
;; execute: they build a single zipper, at the end of the search, where
;; zip-seek builds one at each step.

(define zip-seek-loop
  (x
   (focus treep)
   (path zip-frame-listp))
  :short "@(tsee zip-seek), from a focus and a path."
  (mbe :logic (zip-seek x (zip focus path))
       :exec (if (tree-empty-p focus)
                 (zip focus path)
               (mv-let (equalp ltp)
                       (data::compare-<<
                         x
                         (tree-element->val (tree->head focus)))
                 (cond (equalp
                        (zip focus path))
                       (ltp
                        (zip-seek-loop
                          x
                          (tree->left focus)
                          (cons (zip-frame t
                                           (tree->head focus)
                                           (tree->right focus))
                                path)))
                       (t
                        (zip-seek-loop
                          x
                          (tree->right focus)
                          (cons (zip-frame nil
                                           (tree->head focus)
                                           (tree->left focus))
                                path)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable zip-seek-loop
                                           zip-value
                                           zip-descend-left
                                           zip-descend-right)
                        :expand ((zip-seek x (zip focus path))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-zip-seek-loop
  ((x acl2-numberp)
   (focus treep)
   (path zip-frame-listp))
  :guard (tree-all-acl2-numberp focus)
  :short "A variant of @(tsee zip-seek-loop) for numbers."
  (mbe :logic (zip-seek x (zip focus path))
       :exec (if (tree-empty-p focus)
                 (zip focus path)
               (mv-let (equalp ltp)
                       (data::acl2-number-compare-<<
                         x
                         (tree-element->val (tree->head focus)))
                 (cond (equalp
                        (zip focus path))
                       (ltp
                        (acl2-number-zip-seek-loop
                          x
                          (tree->left focus)
                          (cons (zip-frame t
                                           (tree->head focus)
                                           (tree->right focus))
                                path)))
                       (t
                        (acl2-number-zip-seek-loop
                          x
                          (tree->right focus)
                          (cons (zip-frame nil
                                           (tree->head focus)
                                           (tree->left focus))
                                path)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable acl2-number-zip-seek-loop
                                           zip-value
                                           zip-descend-left
                                           zip-descend-right
                                           tree-all-acl2-numberp)
                        :expand ((zip-seek x (zip focus path))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-zip-seek-loop
  ((x symbolp)
   (focus treep)
   (path zip-frame-listp))
  :guard (tree-all-symbolp focus)
  :short "A variant of @(tsee zip-seek-loop) for symbols."
  (mbe :logic (zip-seek x (zip focus path))
       :exec (if (tree-empty-p focus)
                 (zip focus path)
               (mv-let (equalp ltp)
                       (data::symbol-compare-<<
                         x
                         (tree-element->val (tree->head focus)))
                 (cond (equalp
                        (zip focus path))
                       (ltp
                        (symbol-zip-seek-loop
                          x
                          (tree->left focus)
                          (cons (zip-frame t
                                           (tree->head focus)
                                           (tree->right focus))
                                path)))
                       (t
                        (symbol-zip-seek-loop
                          x
                          (tree->right focus)
                          (cons (zip-frame nil
                                           (tree->head focus)
                                           (tree->left focus))
                                path)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable symbol-zip-seek-loop
                                           zip-value
                                           zip-descend-left
                                           zip-descend-right
                                           tree-all-symbolp)
                        :expand ((zip-seek x (zip focus path))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-zip-seek-loop
  ((x eqlablep)
   (focus treep)
   (path zip-frame-listp))
  :guard (tree-all-eqlablep focus)
  :short "A variant of @(tsee zip-seek-loop) for @(tsee eqlablep) values."
  (mbe :logic (zip-seek x (zip focus path))
       :exec (if (tree-empty-p focus)
                 (zip focus path)
               (mv-let (equalp ltp)
                       (data::eqlable-compare-<<
                         x
                         (tree-element->val (tree->head focus)))
                 (cond (equalp
                        (zip focus path))
                       (ltp
                        (eqlable-zip-seek-loop
                          x
                          (tree->left focus)
                          (cons (zip-frame t
                                           (tree->head focus)
                                           (tree->right focus))
                                path)))
                       (t
                        (eqlable-zip-seek-loop
                          x
                          (tree->right focus)
                          (cons (zip-frame nil
                                           (tree->head focus)
                                           (tree->left focus))
                                path)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable eqlable-zip-seek-loop
                                           zip-value
                                           zip-descend-left
                                           zip-descend-right
                                           tree-all-eqlablep)
                        :expand ((zip-seek x (zip focus path))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A zipper brackets a value when the nearest value before the focus subtree
;; is below it, and the nearest value after is above it. The search keeps the
;; sought value bracketed.

(local
  (define zip-brackets-p
    (x
     (zip zipp))
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

(defruledl in-of-zip-oset-before-of-zip-seek-when-not-tree-search-in
  (implies (and (bstp (zip-plug (zip-seek x zip)))
                (not (tree-search-in x (zip->focus zip)))
                (zip-brackets-p x zip))
           (equal (set::in y (zip-oset-before (zip-seek x zip)))
                  (and (tree-in y (zip-plug (zip-seek x zip)))
                       (<< y x))))
  :enable (tree-in-becomes-member-equal-of-tree-in-order
           tree-in-order-of-zip-plug-split-at-cursor
           <<-of-car-of-last-of-zip-before-when-zip-brackets-p
           <<-of-arg1-and-car-of-zip-after-when-zip-brackets-p
           data::<<-when-member-equal-and-<<-of-car-of-last
           data::<<-when-member-equal-and-<<-of-arg1-and-car
           data::<<-rules
           acl2::consp-when-member-equal
           not-member-equal-of-zip-before-when-member-equal-of-zip-after)
  :disable (zip-plug-of-zip-seek
            member-equal-of-tree-in-order-under-iff))

(defruledl in-of-zip-oset-after-of-zip-seek-when-not-tree-search-in
  (implies (and (bstp (zip-plug (zip-seek x zip)))
                (not (tree-search-in x (zip->focus zip)))
                (zip-brackets-p x zip))
           (equal (set::in y (zip-oset-after (zip-seek x zip)))
                  (and (tree-in y (zip-plug (zip-seek x zip)))
                       (<< x y))))
  :enable (tree-in-becomes-member-equal-of-tree-in-order
           tree-in-order-of-zip-plug-split-at-cursor
           <<-of-car-of-last-of-zip-before-when-zip-brackets-p
           <<-of-arg1-and-car-of-zip-after-when-zip-brackets-p
           data::<<-when-member-equal-and-<<-of-car-of-last
           data::<<-when-member-equal-and-<<-of-arg1-and-car
           data::<<-rules
           acl2::consp-when-member-equal
           not-member-equal-of-zip-after-when-member-equal-of-zip-before)
  :disable (zip-plug-of-zip-seek
            member-equal-of-tree-in-order-under-iff))

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-zip-oset-before-of-zip-seek-of-zip-root
  (implies (bstp tree)
           (equal (set::in y (zip-oset-before (zip-seek x (zip-root tree))))
                  (and (tree-in y tree)
                       (<< y x))))
  :cases ((tree-in x tree))
  :enable (in-of-zip-oset-before-of-zip-seek-when-not-tree-search-in
           in-of-zip-oset-before-when-bstp))

(defrule in-of-zip-oset-after-of-zip-seek-of-zip-root
  (implies (bstp tree)
           (equal (set::in y (zip-oset-after (zip-seek x (zip-root tree))))
                  (and (tree-in y tree)
                       (<< x y))))
  :cases ((tree-in x tree))
  :enable (in-of-zip-oset-after-of-zip-seek-when-not-tree-search-in
           in-of-zip-oset-after-when-bstp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-path-brackets-p
  (x
   (path zip-frame-listp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check that a value is on the focus side of every frame of a path."
  :long
  (xdoc::topstring-p
    "That is, the value is below the element of each frame entered to the left,
     and above the element of each frame entered to the right. A search for
     the value from the root would take this path.")
  (or (acl2::endp path)
      (and (if (zip-frame->from-left (first path))
               (<< x (tree-element->val (zip-frame->elem (first path))))
             (<< (tree-element->val (zip-frame->elem (first path))) x))
           (zip-path-brackets-p x (rest path)))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-path-brackets-p-when-not-consp-cheap
  (implies (not (consp path))
           (zip-path-brackets-p x path))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable zip-path-brackets-p)

(defrule zip-path-brackets-p-of-path-of-zip-seek
  (implies (zip-path-brackets-p x (zip->path zip))
           (zip-path-brackets-p x (zip->path (zip-seek x zip))))
  :induct (zip-seek x zip)
  :enable (zip-seek
           zip-path-brackets-p
           zip-value
           data::<<-rules))

;; The elements of the focus are bracketed by the path, in a search tree.

(defruledl zip-path-brackets-p-when-tree-in
  (implies (and (bstp (zip-path-plug path tree))
                (tree-in x tree))
           (zip-path-brackets-p x path))
  :induct (zip-path-plug path tree)
  :expand ((zip-path-plug path tree))
  :enable ((:induction zip-path-plug)
           zip-frame-plug
           zip-path-brackets-p
           <<-when-<<-all-l-and-tree-in
           <<-when-<<-all-r-and-tree-in))

(defrule zip-path-brackets-p-of-zip-value-and-path
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (zip-path-brackets-p (zip-value zip) (zip->path zip)))
  :use (:instance zip-path-brackets-p-when-tree-in
                  (x (zip-value zip))
                  (path (zip->path zip))
                  (tree (zip->focus zip)))
  :enable (zip-plug
           zip-value))

;;;;;;;;;;;;;;;;;;;;

;; A search from the root for a value which a path brackets passes through the
;; position of that path.

(local
  (define zip-ascend-induction ((zip zipp))
    :verify-guards nil
    :enabled t
    (if (acl2::endp (zip->path zip))
        zip
      (zip-ascend-induction (zip-ascend-one zip)))
    :measure (len (zip->path zip))))

(defruledl zip-seek-of-zip-ascend-one
  (implies (and (consp (zip->path zip))
                (zip-path-brackets-p x (zip->path zip)))
           (equal (zip-seek x (zip-ascend-one zip))
                  (zip-seek x zip)))
  :expand ((zip-seek x (zip-ascend-one zip))
           (zip-path-brackets-p x (zip->path zip)))
  :enable (zip-value
           zip-frame-plug
           zip-descend-left-of-zip-ascend-one-when-from-left
           zip-descend-right-of-zip-ascend-one-when-not-from-left
           data::<<-rules))

(defruled zip-seek-of-zip-root-of-zip-plug
  (implies (zip-path-brackets-p x (zip->path zip))
           (equal (zip-seek x (zip-root (zip-plug zip)))
                  (zip-seek x zip)))
  :induct (zip-ascend-induction zip)
  :enable (zip-seek-of-zip-ascend-one
           zip-path-brackets-p
           zip-root
           zip-plug))
