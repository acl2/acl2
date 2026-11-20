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

(include-book "../../internal/tree-defs")
(include-book "../../internal/bst-defs")
(include-book "../../internal/heap-defs")
(include-book "../../internal/keys-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")
(include-book "zip-side-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/hash" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))

(local (include-book "../../internal/tree"))
(local (include-book "../../internal/bst"))
(local (include-book "../../internal/heap"))
(local (include-book "../../internal/keys"))
(local (include-book "zip-frame"))
(local (include-book "zipper"))
(local (include-book "zip-side"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (xdoc::set-default-parents zipper))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-update-entry
  (val
   (zip zipp))
  :guard (not (tree-empty-p (zip->focus zip)))
  :returns (zip$ zipp)
  :short "Replace the value of the element the zipper is at."
  :long
  (xdoc::topstring
   (xdoc::p
     "The element keeps its key and hash, so every node keeps its place.
      Logically, a zipper at a hole is left as it is.")
   (xdoc::p
     "Time complexity: @($O(1)$)."))
  (let ((focus (zip->focus zip)))
    (if (mbt (not (tree-empty-p focus)))
        (let ((head (tree->head focus)))
          (zip (tree-node-with-hint (tree-element (tree-element->hash head)
                                                  (tree-element->key head)
                                                  val)
                                    (tree->left focus)
                                    (tree->right focus)
                                    focus)
               (zip->path zip)))
      (zip-fix zip))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-update-entry-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-update-entry val zip0)
                  (zip-update-entry val zip1)))
  :rule-classes :congruence
  :enable zip-update-entry)

(defrule zip->path-of-zip-update-entry
  (equal (zip->path (zip-update-entry val zip))
         (zip->path zip))
  :enable zip-update-entry)

(defrule tree-empty-p-of-focus-of-zip-update-entry
  (equal (tree-empty-p (zip->focus (zip-update-entry val zip)))
         (tree-empty-p (zip->focus zip)))
  :enable zip-update-entry)

(defrule zip-key-of-zip-update-entry
  (equal (zip-key (zip-update-entry val zip))
         (zip-key zip))
  :enable (zip-update-entry
           zip-key))

(defrule zip-val-of-zip-update-entry
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-val (zip-update-entry val zip))
                  val))
  :enable (zip-update-entry
           zip-val))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-tree-before-of-zip-update-entry
  (equal (zip-tree-before (zip-update-entry val zip))
         (zip-tree-before zip))
  :enable (zip-update-entry
           zip-tree-before))

(defrule zip-tree-after-of-zip-update-entry
  (equal (zip-tree-after (zip-update-entry val zip))
         (zip-tree-after zip))
  :enable (zip-update-entry
           zip-tree-after))

(defrule zip-omap-before-of-zip-update-entry
  (equal (zip-omap-before (zip-update-entry val zip))
         (zip-omap-before zip))
  :enable zip-omap-before
  :disable tree-omap-of-zip-tree-before)

(defrule zip-omap-after-of-zip-update-entry
  (equal (zip-omap-after (zip-update-entry val zip))
         (zip-omap-after zip))
  :enable zip-omap-after
  :disable tree-omap-of-zip-tree-after)

(defrule zip-before-of-zip-update-entry
  (equal (zip-before (zip-update-entry val zip))
         (zip-before zip))
  :enable (zip-update-entry
           zip-before))

(defrule zip-after-of-zip-update-entry
  (equal (zip-after (zip-update-entry val zip))
         (zip-after zip))
  :enable (zip-update-entry
           zip-after))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The order and heap invariants of a plugged tree depend on the focus only
;; through its keys and its own invariants.

(defruledl equal-of-<<-all-l-when-equal-of-tree-key-sets
  (implies (equal (tree-key-set x) (tree-key-set y))
           (equal (equal (<<-all-l x key) (<<-all-l y key))
                  t))
  :use ((:instance <<-all-l-when-subset-of-tree-key-sets
                   (tree x) (sub y) (x key))
        (:instance <<-all-l-when-subset-of-tree-key-sets
                   (tree y) (sub x) (x key))))

(defruledl equal-of-<<-all-r-when-equal-of-tree-key-sets
  (implies (equal (tree-key-set x) (tree-key-set y))
           (equal (equal (<<-all-r key x) (<<-all-r key y))
                  t))
  :use ((:instance <<-all-r-when-subset-of-tree-key-sets
                   (tree x) (sub y) (x key))
        (:instance <<-all-r-when-subset-of-tree-key-sets
                   (tree y) (sub x) (x key))))

(defruledl equal-of-heap<-all-l-when-equal-of-tree-key-sets
  (implies (equal (tree-key-set x) (tree-key-set y))
           (equal (equal (heap<-all-l x key) (heap<-all-l y key))
                  t))
  :use ((:instance heap<-all-l-when-subset-of-tree-key-sets
                   (tree x) (sub y) (x key))
        (:instance heap<-all-l-when-subset-of-tree-key-sets
                   (tree y) (sub x) (x key))))

(defruledl tree-key-set-of-zip-path-plug-when-equal-of-tree-key-sets
  (implies (equal (tree-key-set new) (tree-key-set tree))
           (equal (tree-key-set (zip-path-plug path new))
                  (tree-key-set (zip-path-plug path tree))))
  :induct (zip-path-plug-bi-induction path tree new)
  :enable ((:induction zip-path-plug-bi-induction)
           zip-path-plug
           zip-frame-plug))

(defruledl bstp-of-zip-path-plug-when-equal-of-tree-key-sets
  (implies (and (equal (tree-key-set new) (tree-key-set tree))
                (equal (bstp new) (bstp tree)))
           (equal (bstp (zip-path-plug path new))
                  (bstp (zip-path-plug path tree))))
  :induct (zip-path-plug-bi-induction path tree new)
  :enable ((:induction zip-path-plug-bi-induction)
           zip-path-plug
           zip-frame-plug
           <<-all-l-when-subset-of-tree-key-sets
           <<-all-r-when-subset-of-tree-key-sets
           equal-of-<<-all-l-when-equal-of-tree-key-sets
           equal-of-<<-all-r-when-equal-of-tree-key-sets))

(defruledl heapp-of-zip-path-plug-when-equal-of-tree-key-sets
  (implies (and (equal (tree-key-set new) (tree-key-set tree))
                (equal (heapp new) (heapp tree)))
           (equal (heapp (zip-path-plug path new))
                  (heapp (zip-path-plug path tree))))
  :induct (zip-path-plug-bi-induction path tree new)
  :enable ((:induction zip-path-plug-bi-induction)
           zip-path-plug
           zip-frame-plug
           heap<-all-l-when-subset-of-tree-key-sets
           equal-of-heap<-all-l-when-equal-of-tree-key-sets))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-key-set-of-focus-of-zip-update-entry
  (equal (tree-key-set (zip->focus (zip-update-entry val zip)))
         (tree-key-set (zip->focus zip)))
  :enable (zip-update-entry
           tree-key-set))

(defrule bstp-of-focus-of-zip-update-entry
  (equal (bstp (zip->focus (zip-update-entry val zip)))
         (bstp (zip->focus zip)))
  :enable (zip-update-entry
           bstp))

(defrule heapp-of-focus-of-zip-update-entry
  (equal (heapp (zip->focus (zip-update-entry val zip)))
         (heapp (zip->focus zip)))
  :enable (zip-update-entry
           heapp))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-key-set-of-zip-plug-of-zip-update-entry
  (equal (tree-key-set (zip-plug (zip-update-entry val zip)))
         (tree-key-set (zip-plug zip)))
  :use (:instance tree-key-set-of-zip-path-plug-when-equal-of-tree-key-sets
                  (path (zip->path zip))
                  (tree (zip->focus zip))
                  (new (zip->focus (zip-update-entry val zip))))
  :enable zip-plug)

(defrule bstp-of-zip-plug-of-zip-update-entry
  (equal (bstp (zip-plug (zip-update-entry val zip)))
         (bstp (zip-plug zip)))
  :use (:instance bstp-of-zip-path-plug-when-equal-of-tree-key-sets
                  (path (zip->path zip))
                  (tree (zip->focus zip))
                  (new (zip->focus (zip-update-entry val zip))))
  :enable zip-plug)

(defrule heapp-of-zip-plug-of-zip-update-entry
  (equal (heapp (zip-plug (zip-update-entry val zip)))
         (heapp (zip-plug zip)))
  :use (:instance heapp-of-zip-path-plug-when-equal-of-tree-key-sets
                  (path (zip->path zip))
                  (tree (zip->focus zip))
                  (new (zip->focus (zip-update-entry val zip))))
  :enable zip-plug)
