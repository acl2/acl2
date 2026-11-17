; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/defrule" :dir :system)
(include-book "kestrel/data/utilities/omap-defs" :dir :system)
(include-book "kestrel/data/tset/in-defs" :dir :system)

(include-book "../../internal/tree-defs")
(include-book "../../internal/bst-defs")
(include-book "../../internal/keys-defs")
(include-book "../../internal/lookup-defs")
(include-book "zipper-defs")
(include-book "zip-side-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/in" :dir :system))

(local (include-book "kestrel/data/utilities/omap" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

(local (include-book "kestrel/lists-light/append" :dir :system))

(local (include-book "../../internal/in-order"))
(local (include-book "../../internal/keys"))
(local (include-book "../../internal/lookup"))
(local (include-book "zip-side"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The in-order sequence of a search tree is an omap. These put that fact,
;; cut at the cursor, where the omap rules about append can find it.

(defruledl append-of-zip-before-and-zip-after-when-tree-empty-p
  (implies (tree-empty-p (zip->focus zip))
           (equal (append (zip-before zip)
                          (zip-after zip))
                  (tree-in-order (zip-plug zip))))
  :enable tree-in-order-of-zip-plug-split-at-cursor)

(defruledl append-of-zip-before-and-cons-of-zip-key+val-and-zip-after
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (append (zip-before zip)
                          (cons (zip-key+val zip)
                                (zip-after zip)))
                  (tree-in-order (zip-plug zip))))
  :enable tree-in-order-of-zip-plug-split-at-cursor)

(defrulel omapp-of-append-of-sides-when-tree-empty-p-forward-chaining
  (implies (and (bstp (zip-plug zip))
                (tree-empty-p (zip->focus zip)))
           (omap::mapp (append (zip-before zip)
                               (zip-after zip))))
  :rule-classes :forward-chaining
  :enable append-of-zip-before-and-zip-after-when-tree-empty-p
  :disable tree-in-order-of-zip-plug)

(defrulel omapp-of-append-of-sides-when-not-tree-empty-p-forward-chaining
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (and (omap::mapp (append (zip-before zip)
                                    (cons (zip-key+val zip)
                                          (zip-after zip))))
                (omap::mapp (append (append (zip-before zip)
                                            (list (zip-key+val zip)))
                                    (zip-after zip)))))
  :rule-classes :forward-chaining
  :enable append-of-zip-before-and-cons-of-zip-key+val-and-zip-after
  :disable tree-in-order-of-zip-plug)

;;;;;;;;;;;;;;;;;;;;

(defrule omapp-of-zip-before-when-bstp
  (implies (bstp (zip-plug zip))
           (omap::mapp (zip-before zip)))
  :cases ((tree-empty-p (zip->focus zip)))
  :enable data::omapp-of-prefix-when-omapp-of-append)

(defrule omapp-of-zip-after-when-bstp
  (implies (bstp (zip-plug zip))
           (omap::mapp (zip-after zip)))
  :cases ((tree-empty-p (zip->focus zip)))
  :enable data::omapp-of-suffix-when-omapp-of-append)

(defrule not-assoc-equal-of-zip-key-and-zip-before
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (not (assoc-equal (zip-key zip) (zip-before zip))))
  :enable data::not-assoc-equal-of-prefix-when-omapp-of-append)

(defrule not-assoc-equal-of-zip-key-and-zip-after
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (not (assoc-equal (zip-key zip) (zip-after zip))))
  :enable data::not-assoc-equal-of-suffix-when-omapp-of-append)

;; Over a search tree, each side holds the entries of the tree on that side of
;; the cursor's key.

(defruledl assoc-equal-of-zip-before-under-iff-when-bstp
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (iff (assoc-equal key (zip-before zip))
                (and (tset::in key (tree-key-set (zip-plug zip)))
                     (<< key (zip-key zip)))))
  :enable (in-of-tree-key-set-becomes-assoc-equal-of-tree-in-order
           tree-in-order-of-zip-plug-split-at-cursor
           data::<<-across-append-of-keys-when-omapp
           data::not-assoc-equal-of-prefix-when-omapp-of-append
           data::<<-rules))

(defruledl assoc-equal-of-zip-after-under-iff-when-bstp
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (iff (assoc-equal key (zip-after zip))
                (and (tset::in key (tree-key-set (zip-plug zip)))
                     (<< (zip-key zip) key))))
  :enable (in-of-tree-key-set-becomes-assoc-equal-of-tree-in-order
           tree-in-order-of-zip-plug-split-at-cursor
           data::<<-across-append-of-keys-when-omapp
           data::not-assoc-equal-of-suffix-when-omapp-of-append
           data::<<-rules))

(defrule assoc-equal-of-zip-before-when-bstp
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (equal (assoc-equal key (zip-before zip))
                  (if (and (tset::in key (tree-key-set (zip-plug zip)))
                           (<< key (zip-key zip)))
                      (cons key (tree-lookup key (zip-plug zip)))
                    nil)))
  :use (:instance assoc-equal-of-tree-in-order-when-bstp
                  (tree (zip-plug zip)))
  :enable (assoc-equal-of-zip-before-under-iff-when-bstp
           tree-in-order-of-zip-plug-split-at-cursor)
  :disable (assoc-equal-of-tree-in-order-when-bstp
            tree-in-order-of-zip-plug))

(defrule assoc-equal-of-zip-after-when-bstp
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (equal (assoc-equal key (zip-after zip))
                  (if (and (tset::in key (tree-key-set (zip-plug zip)))
                           (<< (zip-key zip) key))
                      (cons key (tree-lookup key (zip-plug zip)))
                    nil)))
  :cases ((assoc-equal key (zip-after zip)))
  :use (:instance assoc-equal-of-tree-in-order-when-bstp
                  (tree (zip-plug zip)))
  :enable (assoc-equal-of-zip-after-under-iff-when-bstp
           assoc-equal-of-zip-before-under-iff-when-bstp
           tree-in-order-of-zip-plug-split-at-cursor
           data::<<-rules)
  :disable (assoc-equal-of-tree-in-order-when-bstp
            tree-in-order-of-zip-plug))

(defrule assoc-of-zip-omap-before-when-bstp
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (equal (omap::assoc key (zip-omap-before zip))
                  (if (and (tset::in key (tree-key-set (zip-plug zip)))
                           (<< key (zip-key zip)))
                      (cons key (tree-lookup key (zip-plug zip)))
                    nil)))
  :enable (zip-omap-before-becomes-zip-before
           data::omap-assoc-becomes-assoc-equal))

(defrule assoc-of-zip-omap-after-when-bstp
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (equal (omap::assoc key (zip-omap-after zip))
                  (if (and (tset::in key (tree-key-set (zip-plug zip)))
                           (<< (zip-key zip) key))
                      (cons key (tree-lookup key (zip-plug zip)))
                    nil)))
  :enable (zip-omap-after-becomes-zip-after
           data::omap-assoc-becomes-assoc-equal))

(defruled not-assoc-equal-of-zip-before-when-assoc-equal-of-zip-after
  (implies (and (assoc-equal key (zip-after zip))
                (bstp (zip-plug zip)))
           (not (assoc-equal key (zip-before zip))))
  :cases ((tree-empty-p (zip->focus zip)))
  :enable (data::not-assoc-equal-of-prefix-when-omapp-of-append
           data::<<-rules))

(defruled not-assoc-equal-of-zip-after-when-assoc-equal-of-zip-before
  (implies (and (assoc-equal key (zip-before zip))
                (bstp (zip-plug zip)))
           (not (assoc-equal key (zip-after zip))))
  :enable not-assoc-equal-of-zip-before-when-assoc-equal-of-zip-after)

(defruled <<-when-assoc-equal-of-zip-before-and-zip-after
  (implies (and (assoc-equal x (zip-before zip))
                (assoc-equal y (zip-after zip))
                (bstp (zip-plug zip)))
           (<< x y))
  :cases ((tree-empty-p (zip->focus zip)))
  :enable (data::<<-across-append-of-keys-when-omapp
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

;; Over a search tree, an entry of either side is the tree's entry for its
;; key. Unlike the rules above, these also hold at a hole.

(defruled assoc-equal-of-zip-before-when-assoc-equal-and-bstp
  (implies (and (assoc-equal key (zip-before zip))
                (bstp (zip-plug zip)))
           (equal (assoc-equal key (zip-before zip))
                  (cons key (tree-lookup key (zip-plug zip)))))
  :cases ((tree-empty-p (zip->focus zip)))
  :use (:instance assoc-equal-of-tree-in-order-when-bstp
                  (tree (zip-plug zip)))
  :enable tree-in-order-of-zip-plug-split-at-cursor
  :disable (assoc-equal-of-tree-in-order-when-bstp
            tree-in-order-of-zip-plug))

(defruled assoc-equal-of-zip-after-when-assoc-equal-and-bstp
  (implies (and (assoc-equal key (zip-after zip))
                (bstp (zip-plug zip)))
           (equal (assoc-equal key (zip-after zip))
                  (cons key (tree-lookup key (zip-plug zip)))))
  :cases ((tree-empty-p (zip->focus zip)))
  :use (:instance assoc-equal-of-tree-in-order-when-bstp
                  (tree (zip-plug zip)))
  :enable (tree-in-order-of-zip-plug-split-at-cursor
           not-assoc-equal-of-zip-before-when-assoc-equal-of-zip-after)
  :disable (assoc-equal-of-tree-in-order-when-bstp
            tree-in-order-of-zip-plug))

;;;;;;;;;;;;;;;;;;;;

;; The keys of the tree, cut at the cursor.

(defruled in-of-tree-key-set-of-zip-plug-split-at-cursor
  (equal (tset::in key (tree-key-set (zip-plug zip)))
         (or (and (assoc-equal key (zip-before zip)) t)
             (and (not (tree-empty-p (zip->focus zip)))
                  (equal key (zip-key zip)))
             (and (assoc-equal key (zip-after zip)) t)))
  :enable (in-of-tree-key-set-becomes-assoc-equal-of-tree-in-order
           tree-in-order-of-zip-plug-split-at-cursor))

(defrule in-of-tree-key-set-of-zip-key-and-zip-plug
  (implies (not (tree-empty-p (zip->focus zip)))
           (tset::in (zip-key zip) (tree-key-set (zip-plug zip))))
  :enable in-of-tree-key-set-of-zip-plug-split-at-cursor)

(defrule tree-lookup-of-zip-key-and-zip-plug
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (equal (tree-lookup (zip-key zip) (zip-plug zip))
                  (zip-val zip)))
  :use (:instance assoc-equal-of-tree-in-order-when-bstp
                  (key (zip-key zip))
                  (tree (zip-plug zip)))
  :enable (tree-in-order-of-zip-plug-split-at-cursor
           zip-key+val-becomes-cons-of-zip-key-and-zip-val
           data::<<-rules)
  :disable (assoc-equal-of-tree-in-order-when-bstp
            tree-in-order-of-zip-plug))
