; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/internal/tree-defs" :dir :system)
(include-book "kestrel/data/treeset/internal/bst-defs" :dir :system)
(include-book "kestrel/data/treeset/internal/in-defs" :dir :system)
(include-book "kestrel/data/treeset/internal/split-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)

(include-book "tree-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "join-defs")
(include-book "split-defs")
(include-book "submap-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/internal/tree" :dir :system))
(local (include-book "kestrel/data/treeset/internal/bst" :dir :system))
(local (include-book "kestrel/data/treeset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/treeset/internal/heap" :dir :system))
(local (include-book "kestrel/data/treeset/internal/in" :dir :system))
(local (include-book "kestrel/data/treeset/internal/split" :dir :system))
(local (include-book "kestrel/data/treeset/hash" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/generic-typed" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

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
  ((keys treeset::treep)
   (tree treep))
  :parents (implementation)
  :short "Take the restriction of a map treap under a key set treap."
  :long
  (xdoc::topstring
   (xdoc::p
     "The result might not be the expected restriction if the input trees are
      not binary search trees."))
  :returns (tree treep)
  (cond ((or (treeset::tree-empty-p keys)
             (tree-empty-p tree))
         nil)
        ((heap<-with-hashes (treeset::tree-element->val
                              (treeset::tree->head keys))
                            (tree-element->key (tree->head tree))
                            (treeset::tree-element->hash
                              (treeset::tree->head keys))
                            (tree-element->hash (tree->head tree)))
         (mv-let (in left right)
                 (treeset::tree-split (tree-element->key (tree->head tree)) keys)
           (let ((left (tree-restrict left (tree->left tree)))
                 (right (tree-restrict right (tree->right tree))))
             (if in
                 (tree-node (tree->head tree) left right)
               (mbe :logic (tree-join-at (tree-element->key (tree->head tree))
                                         left right)
                    :exec (tree-join left right))))))
        (t
         (mv-let (assoc left right)
                 (tree-split (treeset::tree-element->val
                               (treeset::tree->head keys))
                             tree)
           (let ((left (tree-restrict (treeset::tree->left keys) left))
                 (right (tree-restrict (treeset::tree->right keys) right)))
             (if assoc
                 (tree-node
                   (mbe :logic (tree-element
                                 (treeset::tree-element->hash
                                   (treeset::tree->head keys))
                                 (treeset::tree-element->val
                                   (treeset::tree->head keys))
                                 (cdr assoc))
                        :exec (cons (treeset::tree-element->hash
                                      (treeset::tree->head keys))
                                    assoc))
                   left
                   right)
               (mbe :logic (tree-join-at
                             (treeset::tree-element->val
                               (treeset::tree->head keys))
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

(in-theory (disable (:t tree-restrict)))

(defrule tree-restrict-type-prescription
  (or (consp (tree-restrict keys tree))
      (equal (tree-restrict keys tree) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-restrict)

(defrule tree-restrict-when-tree-equiv-of-arg1-congruence
  (implies (treeset::tree-equiv x0 x1)
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
  (implies (treeset::tree-empty-p keys)
           (tree-empty-p (tree-restrict keys tree)))
  :enable tree-restrict)

(defrule tree-empty-p-of-tree-restrict-when-tree-empty-p-of-arg2
  (implies (tree-empty-p tree)
           (tree-empty-p (tree-restrict keys tree)))
  :enable tree-restrict)

(defrule not-tree-restrict-when-tree-empty-p-of-arg1
  (implies (treeset::tree-empty-p keys)
           (not (tree-restrict keys tree)))
  :enable tree-restrict)

(defrule not-tree-restrict-when-tree-empty-p-of-arg2
  (implies (tree-empty-p tree)
           (not (tree-restrict keys tree)))
  :enable tree-restrict)

(defrule in-of-tree-key-set-of-tree-restrict
  (implies (and (treeset::bstp keys)
                (bstp tree))
           (equal (treeset::in a (tree-key-set (tree-restrict keys tree)))
                  (and (treeset::tree-in a keys)
                       (treeset::in a (tree-key-set tree)))))
  ;; TODO: improve proof
  :induct t
  :enable tree-restrict)

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-restrict
  (implies (and (treeset::<<-all-l keys x)
                (<<-all-l tree x))
           (<<-all-l (tree-restrict keys tree) x))
  :induct t
  :enable tree-restrict)

(defrule <<-all-r-of-arg1-and-tree-restrict
  (implies (and (treeset::<<-all-r x keys)
                (<<-all-r x tree))
           (<<-all-r x (tree-restrict keys tree)))
  :induct t
  :enable tree-restrict)

;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-tree-restrict-when-bstp
  (implies (and (treeset::bstp keys)
                (bstp tree))
           (bstp (tree-restrict keys tree)))
  :induct t
  :enable tree-restrict)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-lookup-of-tree-restrict
  (implies (and (treeset::bstp keys)
                (bstp tree))
           (equal (tree-lookup key (tree-restrict keys tree))
                  (if (treeset::tree-in key keys)
                      (tree-lookup key tree)
                    nil)))
  ;; TODO: improve proof
  :induct t
  :enable (tree-restrict
           tree-lookup
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-restrict
  (implies (and (treeset::heap<-all-l keys x)
                (heap<-all-l tree x))
           (heap<-all-l (tree-restrict keys tree) x))
  :induct t
  :enable tree-restrict)

;;;;;;;;;;;;;;;;;;;;

(defruled tree->head-when-heapp-and-tree-in-tree->head
  (implies (and (treeset::heapp x)
                (heapp y)
                (treeset::in (treeset::tree-element->val (treeset::tree->head x))
                             (tree-key-set y))
                (treeset::tree-in (tree-element->key (tree->head y)) x))
           (equal (treeset::tree-element->val (treeset::tree->head x))
                  (tree-element->key (tree->head y))))
  :use ((:instance heap<-of-arg1-and-tree->head-when-in-arg1-of-tree-key-set
                   (key (treeset::tree-element->val (treeset::tree->head x)))
                   (tree y)))
  :enable heap<-rules
  :disable heap<-of-arg1-and-tree->head-when-in-arg1-of-tree-key-set)

(defrule heapp-of-tree-restrict-when-bstp-and-heapp
  (implies (and (treeset::bstp keys)
                (bstp tree)
                (treeset::heapp keys)
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
  ((keys treeset::acl2-number-treep)
   (tree acl2-number-treep))
  (mbe :logic (tree-restrict keys tree)
       :exec
       (cond ((or (treeset::tree-empty-p keys)
                  (tree-empty-p tree))
              nil)
             ((heap<-with-hashes (treeset::tree-element->val
                                   (treeset::tree->head keys))
                                 (tree-element->key (tree->head tree))
                                 (treeset::tree-element->hash
                                   (treeset::tree->head keys))
                                 (tree-element->hash (tree->head tree)))
              (mv-let (in left right)
                      (treeset::acl2-number-tree-split
                        (tree-element->key (tree->head tree)) keys)
                (let ((left (acl2-number-tree-restrict left
                                                       (tree->left tree)))
                      (right (acl2-number-tree-restrict right
                                                        (tree->right tree))))
                  (if in
                      (tree-node (tree->head tree) left right)
                    (tree-join left right)))))
             (t
              (mv-let (assoc left right)
                      (acl2-number-tree-split (treeset::tree-element->val
                                                (treeset::tree->head keys))
                                              tree)
                (let ((left (acl2-number-tree-restrict
                              (treeset::tree->left keys) left))
                      (right (acl2-number-tree-restrict
                               (treeset::tree->right keys) right)))
                  (if assoc
                      (tree-node
                        (mbe :logic (tree-element
                                      (treeset::tree-element->hash
                                        (treeset::tree->head keys))
                                      (treeset::tree-element->val
                                        (treeset::tree->head keys))
                                      (cdr assoc))
                             :exec (cons (treeset::tree-element->hash
                                           (treeset::tree->head keys))
                                         assoc))
                        left
                        right)
                    (tree-join left right)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-restrict
                                           acl2-number-tree-restrict
                                           treeset::tree-all-acl2-numberp
                                           tree-keys-acl2-numberp
                                           tree-join-at
                                           tree-element
                                           tree-element-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-restrict
  ((keys treeset::symbol-treep)
   (tree symbol-treep))
  (mbe :logic (tree-restrict keys tree)
       :exec
       (cond ((or (treeset::tree-empty-p keys)
                  (tree-empty-p tree))
              nil)
             ((heap<-with-hashes (treeset::tree-element->val
                                   (treeset::tree->head keys))
                                 (tree-element->key (tree->head tree))
                                 (treeset::tree-element->hash
                                   (treeset::tree->head keys))
                                 (tree-element->hash (tree->head tree)))
              (mv-let (in left right)
                      (treeset::symbol-tree-split
                        (tree-element->key (tree->head tree)) keys)
                (let ((left (symbol-tree-restrict left
                                                       (tree->left tree)))
                      (right (symbol-tree-restrict right
                                                        (tree->right tree))))
                  (if in
                      (tree-node (tree->head tree) left right)
                    (tree-join left right)))))
             (t
              (mv-let (assoc left right)
                      (symbol-tree-split (treeset::tree-element->val
                                                (treeset::tree->head keys))
                                              tree)
                (let ((left (symbol-tree-restrict
                              (treeset::tree->left keys) left))
                      (right (symbol-tree-restrict
                               (treeset::tree->right keys) right)))
                  (if assoc
                      (tree-node
                        (mbe :logic (tree-element
                                      (treeset::tree-element->hash
                                        (treeset::tree->head keys))
                                      (treeset::tree-element->val
                                        (treeset::tree->head keys))
                                      (cdr assoc))
                             :exec (cons (treeset::tree-element->hash
                                           (treeset::tree->head keys))
                                         assoc))
                        left
                        right)
                    (tree-join left right)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-restrict
                                           symbol-tree-restrict
                                           treeset::tree-all-symbolp
                                           tree-keys-symbolp
                                           tree-join-at
                                           tree-element
                                           tree-element-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-restrict
  ((keys treeset::eqlable-treep)
   (tree eqlable-treep))
  (mbe :logic (tree-restrict keys tree)
       :exec
       (cond ((or (treeset::tree-empty-p keys)
                  (tree-empty-p tree))
              nil)
             ((heap<-with-hashes (treeset::tree-element->val
                                   (treeset::tree->head keys))
                                 (tree-element->key (tree->head tree))
                                 (treeset::tree-element->hash
                                   (treeset::tree->head keys))
                                 (tree-element->hash (tree->head tree)))
              (mv-let (in left right)
                      (treeset::eqlable-tree-split
                        (tree-element->key (tree->head tree)) keys)
                (let ((left (eqlable-tree-restrict left
                                                       (tree->left tree)))
                      (right (eqlable-tree-restrict right
                                                        (tree->right tree))))
                  (if in
                      (tree-node (tree->head tree) left right)
                    (tree-join left right)))))
             (t
              (mv-let (assoc left right)
                      (eqlable-tree-split (treeset::tree-element->val
                                                (treeset::tree->head keys))
                                              tree)
                (let ((left (eqlable-tree-restrict
                              (treeset::tree->left keys) left))
                      (right (eqlable-tree-restrict
                               (treeset::tree->right keys) right)))
                  (if assoc
                      (tree-node
                        (mbe :logic (tree-element
                                      (treeset::tree-element->hash
                                        (treeset::tree->head keys))
                                      (treeset::tree-element->val
                                        (treeset::tree->head keys))
                                      (cdr assoc))
                             :exec (cons (treeset::tree-element->hash
                                           (treeset::tree->head keys))
                                         assoc))
                        left
                        right)
                    (tree-join left right)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-restrict
                                           eqlable-tree-restrict
                                           treeset::tree-all-eqlablep
                                           tree-keys-eqlablep
                                           tree-join-at
                                           tree-element
                                           tree-element-p))))
