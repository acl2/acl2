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
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))
(local (include-book "kestrel/data/tset/generic-typed" :dir :system))

(local (include-book "kestrel/data/utilities/omap" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-path-brackets-p
  (key
   (path zip-frame-listp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check that a key is on the focus side of every frame of a path."
  :long
  (xdoc::topstring-p
    "That is, the key is below the element of each frame entered to the left,
     and above the element of each frame entered to the right. A search for
     the key from the root would take this path.")
  (or (acl2::endp path)
      (and (if (zip-frame->from-left (first path))
               (<< key (tree-element->key (zip-frame->elem (first path))))
             (<< (tree-element->key (zip-frame->elem (first path))) key))
           (zip-path-brackets-p key (rest path)))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-path-brackets-p-when-not-consp-cheap
  (implies (not (consp path))
           (zip-path-brackets-p key path))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable zip-path-brackets-p)

(defrule zip-path-brackets-p-of-path-of-zip-seek
  (implies (zip-path-brackets-p x (zip->path zip))
           (zip-path-brackets-p x (zip->path (zip-seek x zip))))
  :induct (zip-seek x zip)
  :enable (zip-seek
           zip-path-brackets-p
           zip-key
           data::<<-rules))

;; The keys of the focus are bracketed by the path, in a search tree.

(defrulel bstp-of-arg2-when-bstp-of-zip-path-plug-forward-chaining
  (implies (bstp (zip-path-plug path tree))
           (bstp tree))
  :rule-classes :forward-chaining)

(defrulel bstp-of-parts-when-bstp-of-tree-node-forward-chaining
  (implies (bstp (tree-node head left right))
           (and (bstp left)
                (bstp right)
                (<<-all-l left (tree-element->key head))
                (<<-all-r (tree-element->key head) right)))
  :rule-classes :forward-chaining)

(local
  (define zip-path-plug-induction ((path zip-frame-listp)
                                   (tree treep))
    :verify-guards nil
    :enabled t
    (if (acl2::endp path)
        tree
      (zip-path-plug-induction (rest path)
                               (zip-frame-plug (first path) tree)))))

(defruled zip-path-brackets-p-when-in-of-tree-key-set
  (implies (and (bstp (zip-path-plug path tree))
                (tset::in key (tree-key-set tree)))
           (zip-path-brackets-p key path))
  :induct (zip-path-plug-induction path tree)
  :expand ((zip-path-plug path tree))
  :enable (zip-frame-plug
           zip-path-brackets-p
           <<-when-<<-all-l-and-in-of-tree-key-set
           <<-when-<<-all-r-and-in-of-tree-key-set))

(defrule zip-path-brackets-p-of-zip-key-and-path
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (zip-path-brackets-p (zip-key zip) (zip->path zip)))
  :use (:instance zip-path-brackets-p-when-in-of-tree-key-set
                  (key (zip-key zip))
                  (path (zip->path zip))
                  (tree (zip->focus zip)))
  :enable (zip-plug
           zip-key))

;;;;;;;;;;;;;;;;;;;;

;; A search from the root for a key which a path brackets passes through the
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
  :enable (zip-key
           zip-frame-plug
           zip-descend-left-of-zip-ascend-one-when-from-left
           zip-descend-right-of-zip-ascend-one-when-not-from-left
           data::<<-rules))

(defrulel zip-of-focus-and-nil-when-not-consp-of-path
  (implies (not (consp (zip->path zip)))
           (equal (zip (zip->focus zip) nil)
                  (zip-fix zip)))
  :use zip-of-zip-accessors
  :disable zip-of-zip-accessors)

(defruled zip-seek-of-zip-root-of-zip-plug
  (implies (zip-path-brackets-p x (zip->path zip))
           (equal (zip-seek x (zip-root (zip-plug zip)))
                  (zip-seek x zip)))
  :induct (zip-ascend-induction zip)
  :enable (zip-seek-of-zip-ascend-one
           zip-path-brackets-p
           zip-root
           zip-plug))
