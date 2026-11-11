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

(include-book "kestrel/data/tset/internal/tree-defs" :dir :system)
(include-book "kestrel/data/tset/internal/bst-defs" :dir :system)
(include-book "kestrel/data/tset/internal/in-defs" :dir :system)
(include-book "kestrel/data/tset/internal/split-defs" :dir :system)
(include-book "kestrel/data/tset/in-defs" :dir :system)

(include-book "tree-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "join-defs")
(include-book "split-defs")
(include-book "submap-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/tset/internal/tree" :dir :system))
(local (include-book "kestrel/data/tset/internal/bst" :dir :system))
(local (include-book "kestrel/data/tset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/tset/internal/heap" :dir :system))
(local (include-book "kestrel/data/tset/internal/in" :dir :system))
(local (include-book "kestrel/data/tset/internal/split" :dir :system))
(local (include-book "kestrel/data/tset/hash" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/generic-typed" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "keys"))
(local (include-book "lookup"))
(local (include-book "join"))
(local (include-book "split"))
(local (include-book "submap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-restrict
  ((keys tset::treep)
   (tree treep))
  :type-prescription :none
  :parents (implementation)
  :short "Take the restriction of a map treap under a key set treap."
  :long
  (xdoc::topstring
   (xdoc::p
     "The result might not be the expected restriction if the input trees are
      not binary search trees."))
  :returns (tree treep)
  (cond ((or (tset::tree-empty-p keys)
             (tree-empty-p tree))
         nil)
        ((heap<-with-hashes (tset::tree-element->val
                              (tset::tree->head keys))
                            (tree-element->key (tree->head tree))
                            (tset::tree-element->hash
                              (tset::tree->head keys))
                            (tree-element->hash (tree->head tree)))
         (mv-let (in left right)
                 (tset::tree-split (tree-element->key (tree->head tree)) keys)
           (let ((left (tree-restrict left (tree->left tree)))
                 (right (tree-restrict right (tree->right tree))))
             (if in
                 (tree-node-with-hint (tree->head tree) left right tree)
               (mbe :logic (tree-join-at (tree-element->key (tree->head tree))
                                         left right)
                    :exec (tree-join left right))))))
        (t
         (mv-let (assoc left right)
                 (tree-split (tset::tree-element->val
                               (tset::tree->head keys))
                             tree)
           (let ((left (tree-restrict (tset::tree->left keys) left))
                 (right (tree-restrict (tset::tree->right keys) right)))
             (if assoc
                 (tree-node
                   (mbe :logic (tree-element
                                 (tset::tree-element->hash
                                   (tset::tree->head keys))
                                 (tset::tree-element->val
                                   (tset::tree->head keys))
                                 (cdr assoc))
                        :exec (cons (tset::tree-element->hash
                                      (tset::tree->head keys))
                                    assoc))
                   left
                   right)
               (mbe :logic (tree-join-at
                             (tset::tree-element->val
                               (tset::tree->head keys))
                             left
                             right)
                    :exec (tree-join left right)))))))
  :measure (+ (acl2-count keys)
              (acl2-count tree))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable tree-join-at
                                           tree-element
                                           tree-element-p))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-restrict-type-prescription
  (or (consp (tree-restrict keys tree))
      (equal (tree-restrict keys tree) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-restrict)

(defrule tree-restrict-when-tree-equiv-of-arg1-congruence
  (implies (tset::tree-equiv x0 x1)
           (equal (tree-restrict x0 z)
                  (tree-restrict x1 z)))
  :rule-classes :congruence
  :induct t
  :enable tree-restrict)

(defrule tree-restrict-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv y0 y1)
           (equal (tree-restrict keys y0)
                  (tree-restrict keys y1)))
  :rule-classes :congruence
  :induct t
  :enable tree-restrict)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-of-tree-restrict-when-tree-empty-p-of-arg1
  (implies (tset::tree-empty-p keys)
           (tree-empty-p (tree-restrict keys tree)))
  :enable tree-restrict)

(defrule tree-empty-p-of-tree-restrict-when-tree-empty-p-of-arg2
  (implies (tree-empty-p tree)
           (tree-empty-p (tree-restrict keys tree)))
  :enable tree-restrict)

(defrule not-tree-restrict-when-tree-empty-p-of-arg1
  (implies (tset::tree-empty-p keys)
           (not (tree-restrict keys tree)))
  :enable tree-restrict)

(defrule not-tree-restrict-when-tree-empty-p-of-arg2
  (implies (tree-empty-p tree)
           (not (tree-restrict keys tree)))
  :enable tree-restrict)

(defrule in-of-tree-key-set-of-tree-restrict
  (implies (and (tset::bstp keys)
                (bstp tree))
           (equal (tset::in a (tree-key-set (tree-restrict keys tree)))
                  (and (tset::tree-in a keys)
                       (tset::in a (tree-key-set tree)))))
  ;; TODO: improve proof
  :induct t
  :enable (tree-restrict
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-restrict
  (implies (and (tset::<<-all-l keys x)
                (<<-all-l tree x))
           (<<-all-l (tree-restrict keys tree) x))
  :induct t
  :enable tree-restrict)

(defrule <<-all-r-of-arg1-and-tree-restrict
  (implies (and (tset::<<-all-r x keys)
                (<<-all-r x tree))
           (<<-all-r x (tree-restrict keys tree)))
  :induct t
  :enable tree-restrict)

;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-tree-restrict-when-bstp
  (implies (and (tset::bstp keys)
                (bstp tree))
           (bstp (tree-restrict keys tree)))
  :induct t
  :enable tree-restrict)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-lookup-of-tree-restrict
  (implies (and (tset::bstp keys)
                (bstp tree))
           (equal (tree-lookup key (tree-restrict keys tree))
                  (if (tset::tree-in key keys)
                      (tree-lookup key tree)
                    nil)))
  ;; TODO: improve proof
  :induct t
  :enable (tree-restrict
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-restrict
  (implies (and (tset::heap<-all-l keys x)
                (heap<-all-l tree x))
           (heap<-all-l (tree-restrict keys tree) x))
  :induct t
  :enable tree-restrict)

;;;;;;;;;;;;;;;;;;;;

(defruled tree->head-when-heapp-and-tree-in-tree->head
  (implies (and (tset::heapp x)
                (heapp y)
                (tset::in (tset::tree-element->val (tset::tree->head x))
                          (tree-key-set y))
                (tset::tree-in (tree-element->key (tree->head y)) x))
           (equal (tset::tree-element->val (tset::tree->head x))
                  (tree-element->key (tree->head y))))
  :use ((:instance heap<-of-arg1-and-tree->head-when-in-arg1-of-tree-key-set
                   (key (tset::tree-element->val (tset::tree->head x)))
                   (tree y)))
  :enable heap<-rules
  :disable heap<-of-arg1-and-tree->head-when-in-arg1-of-tree-key-set)

(defrule heapp-of-tree-restrict-when-bstp-and-heapp
  (implies (and (tset::bstp keys)
                (bstp tree)
                (tset::heapp keys)
                (heapp tree))
           (heapp (tree-restrict keys tree)))
  ;; TODO: why can't this rule just be enabled?
  :hints ('(:use (:instance tree->head-when-heapp-and-tree-in-tree->head
                            (x keys)
                            (y tree))))
  :induct t
  :enable tree-restrict)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-restrict
  ((keys tset::acl2-number-treep)
   (tree acl2-number-treep))
  (mbe :logic (tree-restrict keys tree)
       :exec
       (cond ((or (tset::tree-empty-p keys)
                  (tree-empty-p tree))
              nil)
             ((heap<-with-hashes (tset::tree-element->val
                                   (tset::tree->head keys))
                                 (tree-element->key (tree->head tree))
                                 (tset::tree-element->hash
                                   (tset::tree->head keys))
                                 (tree-element->hash (tree->head tree)))
              (mv-let (in left right)
                      (tset::acl2-number-tree-split
                        (tree-element->key (tree->head tree)) keys)
                (let ((left (acl2-number-tree-restrict left
                                                       (tree->left tree)))
                      (right (acl2-number-tree-restrict right
                                                        (tree->right tree))))
                  (if in
                      (tree-node-with-hint (tree->head tree) left right tree)
                    (tree-join left right)))))
             (t
              (mv-let (assoc left right)
                      (acl2-number-tree-split (tset::tree-element->val
                                                (tset::tree->head keys))
                                              tree)
                (let ((left (acl2-number-tree-restrict
                              (tset::tree->left keys) left))
                      (right (acl2-number-tree-restrict
                               (tset::tree->right keys) right)))
                  (if assoc
                      (tree-node
                        (mbe :logic (tree-element
                                      (tset::tree-element->hash
                                        (tset::tree->head keys))
                                      (tset::tree-element->val
                                        (tset::tree->head keys))
                                      (cdr assoc))
                             :exec (cons (tset::tree-element->hash
                                           (tset::tree->head keys))
                                         assoc))
                        left
                        right)
                    (tree-join left right)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-restrict
                                           acl2-number-tree-restrict
                                           tset::tree-all-acl2-numberp
                                           tree-keys-acl2-numberp
                                           tree-join-at
                                           tree-element
                                           tree-element-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-restrict
  ((keys tset::symbol-treep)
   (tree symbol-treep))
  (mbe :logic (tree-restrict keys tree)
       :exec
       (cond ((or (tset::tree-empty-p keys)
                  (tree-empty-p tree))
              nil)
             ((heap<-with-hashes (tset::tree-element->val
                                   (tset::tree->head keys))
                                 (tree-element->key (tree->head tree))
                                 (tset::tree-element->hash
                                   (tset::tree->head keys))
                                 (tree-element->hash (tree->head tree)))
              (mv-let (in left right)
                      (tset::symbol-tree-split
                        (tree-element->key (tree->head tree)) keys)
                (let ((left (symbol-tree-restrict left
                                                       (tree->left tree)))
                      (right (symbol-tree-restrict right
                                                        (tree->right tree))))
                  (if in
                      (tree-node-with-hint (tree->head tree) left right tree)
                    (tree-join left right)))))
             (t
              (mv-let (assoc left right)
                      (symbol-tree-split (tset::tree-element->val
                                                (tset::tree->head keys))
                                              tree)
                (let ((left (symbol-tree-restrict
                              (tset::tree->left keys) left))
                      (right (symbol-tree-restrict
                               (tset::tree->right keys) right)))
                  (if assoc
                      (tree-node
                        (mbe :logic (tree-element
                                      (tset::tree-element->hash
                                        (tset::tree->head keys))
                                      (tset::tree-element->val
                                        (tset::tree->head keys))
                                      (cdr assoc))
                             :exec (cons (tset::tree-element->hash
                                           (tset::tree->head keys))
                                         assoc))
                        left
                        right)
                    (tree-join left right)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-restrict
                                           symbol-tree-restrict
                                           tset::tree-all-symbolp
                                           tree-keys-symbolp
                                           tree-join-at
                                           tree-element
                                           tree-element-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-restrict
  ((keys tset::eqlable-treep)
   (tree eqlable-treep))
  (mbe :logic (tree-restrict keys tree)
       :exec
       (cond ((or (tset::tree-empty-p keys)
                  (tree-empty-p tree))
              nil)
             ((heap<-with-hashes (tset::tree-element->val
                                   (tset::tree->head keys))
                                 (tree-element->key (tree->head tree))
                                 (tset::tree-element->hash
                                   (tset::tree->head keys))
                                 (tree-element->hash (tree->head tree)))
              (mv-let (in left right)
                      (tset::eqlable-tree-split
                        (tree-element->key (tree->head tree)) keys)
                (let ((left (eqlable-tree-restrict left
                                                       (tree->left tree)))
                      (right (eqlable-tree-restrict right
                                                        (tree->right tree))))
                  (if in
                      (tree-node-with-hint (tree->head tree) left right tree)
                    (tree-join left right)))))
             (t
              (mv-let (assoc left right)
                      (eqlable-tree-split (tset::tree-element->val
                                                (tset::tree->head keys))
                                              tree)
                (let ((left (eqlable-tree-restrict
                              (tset::tree->left keys) left))
                      (right (eqlable-tree-restrict
                               (tset::tree->right keys) right)))
                  (if assoc
                      (tree-node
                        (mbe :logic (tree-element
                                      (tset::tree-element->hash
                                        (tset::tree->head keys))
                                      (tset::tree-element->val
                                        (tset::tree->head keys))
                                      (cdr assoc))
                             :exec (cons (tset::tree-element->hash
                                           (tset::tree->head keys))
                                         assoc))
                        left
                        right)
                    (tree-join left right)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-restrict
                                           eqlable-tree-restrict
                                           tset::tree-all-eqlablep
                                           tree-keys-eqlablep
                                           tree-join-at
                                           tree-element
                                           tree-element-p))))
