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

(include-book "kestrel/data/utilities/omap-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/compare-defs" :dir :system)
(include-book "kestrel/data/tset/in-defs" :dir :system)

(include-book "../../internal/tree-defs")
(include-book "../../internal/bst-defs")
(include-book "../../internal/keys-defs")
(include-book "../../internal/lookup-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")
(include-book "zip-move-defs")
(include-book "zip-side-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/generic-typed" :dir :system))

(local (include-book "kestrel/data/utilities/omap" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (include-book "../../internal/tree"))
(local (include-book "../../internal/bst"))
(local (include-book "../../internal/keys"))
(local (include-book "../../internal/lookup"))
(local (include-book "../../internal/in-order"))
(local (include-book "zip-frame"))
(local (include-book "zipper"))
(local (include-book "zip-move"))
(local (include-book "zip-side"))
(local (include-book "zip-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

(defrulel consp-when-assoc-equal-forward-chaining
  (implies (assoc-equal x l)
           (consp l))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (xdoc::set-default-parents zipper))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-seek
  (x
   (zip zipp))
  :returns (zip$ zipp)
  :short "Move the focus to a key within it, or to the hole where the key
          would be."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is the search of @(tsee tree-search-assoc), which assumes that the
      focus is a search tree.")
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth descended, and so
      @($O(\\log(n))$) over a @(see tmap)."))
  (if (tree-empty-p (zip->focus zip))
      (zip-fix zip)
    (mv-let (equalp ltp)
            (data::compare-<< x (zip-key zip))
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
         (not (tree-search-assoc x (zip->focus zip))))
  :induct (zip-seek x zip)
  :enable (zip-seek
           tree-search-assoc
           zip-key))

(defrule zip-key-of-zip-seek
  (implies (tree-search-assoc x (zip->focus zip))
           (equal (zip-key (zip-seek x zip))
                  x))
  :induct (zip-seek x zip)
  :enable (zip-seek
           tree-search-assoc
           zip-key))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-zip-seek
  ((x acl2-numberp)
   (zip zipp))
  :guard (tree-keys-acl2-numberp (zip->focus zip))
  (mbe :logic (zip-seek x zip)
       :exec (if (tree-empty-p (zip->focus zip))
                 zip
               (mv-let (equalp ltp)
                       (data::acl2-number-compare-<< x (zip-key zip))
                 (cond (equalp zip)
                       (ltp (acl2-number-zip-seek x (zip-descend-left zip)))
                       (t (acl2-number-zip-seek x (zip-descend-right zip)))))))
  :enabled t
  :guard-hints
  (("Goal"
    :in-theory (enable zip-seek
                       acl2-number-zip-seek
                       zip-key
                       tset::set-all-acl2-numberp-when-set-all-acl2-numberp-and-subset))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-zip-seek
  ((x symbolp)
   (zip zipp))
  :guard (tree-keys-symbolp (zip->focus zip))
  (mbe :logic (zip-seek x zip)
       :exec (if (tree-empty-p (zip->focus zip))
                 zip
               (mv-let (equalp ltp)
                       (data::symbol-compare-<< x (zip-key zip))
                 (cond (equalp zip)
                       (ltp (symbol-zip-seek x (zip-descend-left zip)))
                       (t (symbol-zip-seek x (zip-descend-right zip)))))))
  :enabled t
  :guard-hints
  (("Goal"
    :in-theory (enable zip-seek
                       symbol-zip-seek
                       zip-key
                       tset::set-all-symbolp-when-set-all-symbolp-and-subset))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-zip-seek
  ((x eqlablep)
   (zip zipp))
  :guard (tree-keys-eqlablep (zip->focus zip))
  (mbe :logic (zip-seek x zip)
       :exec (if (tree-empty-p (zip->focus zip))
                 zip
               (mv-let (equalp ltp)
                       (data::eqlable-compare-<< x (zip-key zip))
                 (cond (equalp zip)
                       (ltp (eqlable-zip-seek x (zip-descend-left zip)))
                       (t (eqlable-zip-seek x (zip-descend-right zip)))))))
  :enabled t
  :guard-hints
  (("Goal"
    :in-theory (enable zip-seek
                       eqlable-zip-seek
                       zip-key
                       tset::set-all-eqlablep-when-set-all-eqlablep-and-subset))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A zipper brackets a key when the nearest key before the focus subtree is
;; below it, and the nearest key after is above it. The search keeps the
;; sought key bracketed.

(local
  (define zip-brackets-p
    (x
     (zip zipp))
    :returns (yes/no booleanp :rule-classes :type-prescription)
    :verify-guards nil
    (let ((before (zip-path-before (zip->path zip)))
          (after (zip-path-after (zip->path zip))))
      (and (or (not (consp before))
               (<< (caar (last before)) x))
           (or (not (consp after))
               (<< x (caar after)))))))

(defrulel zip-brackets-p-of-zip-root
  (zip-brackets-p x (zip-root tree))
  :enable zip-brackets-p)

(defrulel zip-brackets-p-of-zip-seek
  (implies (zip-brackets-p x zip)
           (zip-brackets-p x (zip-seek x zip)))
  :induct (zip-seek x zip)
  :enable (zip-seek
           zip-brackets-p
           zip-key
           data::<<-rules))

(defruledl <<-of-caar-of-last-of-zip-before-when-zip-brackets-p
  (implies (and (zip-brackets-p x zip)
                (tree-empty-p (zip->focus zip))
                (consp (zip-before zip)))
           (<< (caar (last (zip-before zip))) x))
  :enable (zip-brackets-p
           zip-before))

(defruledl <<-of-arg1-and-caar-of-zip-after-when-zip-brackets-p
  (implies (and (zip-brackets-p x zip)
                (tree-empty-p (zip->focus zip))
                (consp (zip-after zip)))
           (<< x (caar (zip-after zip))))
  :enable (zip-brackets-p
           zip-after))

;;;;;;;;;;;;;;;;;;;;

;; So at the hole of an unsuccessful search, the entries before are those with
;; keys below the sought key, and the entries after are those with keys above
;; it.

(defruledl assoc-equal-of-zip-before-of-zip-seek-when-not-tree-search-assoc
  (implies (and (bstp (zip-plug (zip-seek x zip)))
                (not (tree-search-assoc x (zip->focus zip)))
                (zip-brackets-p x zip))
           (equal (assoc-equal key (zip-before (zip-seek x zip)))
                  (if (and (tset::in key
                                     (tree-key-set (zip-plug (zip-seek x zip))))
                           (<< key x))
                      (cons key (tree-lookup key (zip-plug (zip-seek x zip))))
                    nil)))
  :cases ((assoc-equal key (zip-before (zip-seek x zip))))
  :enable (in-of-tree-key-set-of-zip-plug-split-at-cursor
           assoc-equal-of-zip-before-when-assoc-equal-and-bstp
           <<-of-caar-of-last-of-zip-before-when-zip-brackets-p
           <<-of-arg1-and-caar-of-zip-after-when-zip-brackets-p
           data::<<-when-assoc-equal-and-<<-of-caar-of-last
           data::<<-when-assoc-equal-and-<<-of-arg1-and-caar
           data::<<-rules)
  :disable zip-plug-of-zip-seek)

(defruledl assoc-equal-of-zip-after-of-zip-seek-when-not-tree-search-assoc
  (implies (and (bstp (zip-plug (zip-seek x zip)))
                (not (tree-search-assoc x (zip->focus zip)))
                (zip-brackets-p x zip))
           (equal (assoc-equal key (zip-after (zip-seek x zip)))
                  (if (and (tset::in key
                                     (tree-key-set (zip-plug (zip-seek x zip))))
                           (<< x key))
                      (cons key (tree-lookup key (zip-plug (zip-seek x zip))))
                    nil)))
  :cases ((assoc-equal key (zip-after (zip-seek x zip))))
  :enable (in-of-tree-key-set-of-zip-plug-split-at-cursor
           assoc-equal-of-zip-after-when-assoc-equal-and-bstp
           <<-of-caar-of-last-of-zip-before-when-zip-brackets-p
           <<-of-arg1-and-caar-of-zip-after-when-zip-brackets-p
           data::<<-when-assoc-equal-and-<<-of-caar-of-last
           data::<<-when-assoc-equal-and-<<-of-arg1-and-caar
           data::<<-rules)
  :disable zip-plug-of-zip-seek)

;;;;;;;;;;;;;;;;;;;;

(defrule assoc-of-zip-omap-before-of-zip-seek-of-zip-root
  (implies (bstp tree)
           (equal (omap::assoc key
                               (zip-omap-before (zip-seek x (zip-root tree))))
                  (if (and (tset::in key (tree-key-set tree))
                           (<< key x))
                      (cons key (tree-lookup key tree))
                    nil)))
  :cases ((tset::in x (tree-key-set tree)))
  :enable (assoc-equal-of-zip-before-of-zip-seek-when-not-tree-search-assoc
           zip-omap-before-becomes-zip-before
           data::omap-assoc-becomes-assoc-equal))

(defrule assoc-of-zip-omap-after-of-zip-seek-of-zip-root
  (implies (bstp tree)
           (equal (omap::assoc key
                               (zip-omap-after (zip-seek x (zip-root tree))))
                  (if (and (tset::in key (tree-key-set tree))
                           (<< x key))
                      (cons key (tree-lookup key tree))
                    nil)))
  :cases ((tset::in x (tree-key-set tree)))
  :enable (assoc-equal-of-zip-after-of-zip-seek-when-not-tree-search-assoc
           zip-omap-after-becomes-zip-after
           data::omap-assoc-becomes-assoc-equal))
