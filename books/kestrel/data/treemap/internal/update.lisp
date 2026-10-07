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

(include-book "kestrel/data/treeset/hash-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)

(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "tree-defs")
(include-book "rotate-defs")
(include-book "count-defs")
(include-book "keys-defs")
(include-book "lookup-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/treeset/hash" :dir :system))
(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/generic-typed" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "kestrel/data/utilities/fixed-size-words/u32" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/min" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "count"))
(local (include-book "rotate"))
(local (include-book "keys"))
(local (include-book "lookup"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-update
  (key
   val
   (tree treep))
  (declare (xargs :type-prescription :none))
  ;; TODO: treeset definition should have guards/returns first like this.
  :returns (tree$ treep)
  :parents (implementation)
  :short "Add a key/value pair to the tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "The key/value pair is inserted with respect to the binary search tree
      ordering and then rebalanced with respect to the @(tsee heapp)
      property.")
   (xdoc::p
     "The hash of @('key') is computed lazily, only once the insertion point
      has been found. In particular, if @('key') is already present in the
      tree, it is never hashed: the replacement element reuses the hash stored
      in the existing node. The rebalancing on the way back up compares the
      hashes stored in the nodes, so no further hashing is required. See
      @(tsee tree-update-with-hash) for a variant which accepts a precomputed
      hash."))
  (if (tree-empty-p tree)
      (tree-node (tree-element (hash key) key val) nil nil)
    (let* ((head (tree->head tree))
           (head-key (tree-element->key head)))
      ;; TODO: Should the << check come first? Most of the time, key and
      ;; head-key are not equal. If so, make the same change to treesets.
      ;; - Actually, we probably want a function that returns :lt, :eq, or :gt.
      ;;   Need better tests first though.
      (cond ((equal key head-key)
             (tree-node (tree-element (tree-element->hash head) key val)
                        (tree->left tree)
                        (tree->right tree)))
            ((<< key head-key)
             (let* ((left$ (tree-update key val (tree->left tree)))
                    (head-left$ (tree->head left$))
                    (tree$ (tree-node head
                                      left$
                                      (tree->right tree))))
               (if (heap<-with-hashes
                     head-key
                     (tree-element->key head-left$)
                     (tree-element->hash head)
                     (tree-element->hash head-left$))
                   (rotate-right tree$)
                 tree$)))
            (t
             (let* ((right$ (tree-update key val (tree->right tree)))
                    (head-right$ (tree->head right$))
                    (tree$ (tree-node head
                                      (tree->left tree)
                                      right$)))
               (if (heap<-with-hashes
                     head-key
                     (tree-element->key head-right$)
                     (tree-element->hash head)
                     (tree-element->hash head-right$))
                   (rotate-left tree$)
                 tree$))))))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-of-tree-update
  (not (tree-empty-p (tree-update x val tree)))
  :induct t
  :enable tree-update)

(verify-guards tree-update)

(defrule tree-update-type-prescription
  (consp (tree-update x val tree))
  :rule-classes :type-prescription
  :use tree-empty-p-of-tree-update
  :enable tree-empty-p
  :disable tree-empty-p-of-tree-update)

(defrule tree-update-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-update x val tree0)
                  (tree-update x val tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-update)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-key-set-of-tree-update
  (equal (tree-key-set (tree-update key val tree))
         (treeset::insert key (tree-key-set tree)))
  :induct t
  :enable (tree-update
           tree-key-set))

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-update
  (equal (<<-all-l (tree-update y val tree) x)
         (and (<< y x)
              (<<-all-l tree x)))
  :induct t
  :enable (<<-all-l
           tree-update))

(defrule <<-all-r-of-tree-update
  (equal (<<-all-r x (tree-update y val tree))
         (and (<< x y)
              (<<-all-r x tree)))
  :induct t
  :enable (<<-all-r
           tree-update))

(defrule bstp-of-tree-update-when-bstp
  (implies (bstp tree)
           (bstp (tree-update key val tree)))
  :induct t
  :enable (tree-update
           bstp
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-lookup-of-tree-update
  (implies (bstp tree)
           (equal (tree-lookup x (tree-update y val tree))
                  (if (equal x y)
                      val
                    (tree-lookup x tree))))
  :induct (tree-update y val tree)
  :enable (tree-update
           tree-lookup
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-update
  (equal (heap<-all-l (tree-update y val tree) x)
         (and (heap< y x)
              (heap<-all-l tree x)))
  :induct t
  :enable (heap<-all-l
           tree-update))

;;;;;;;;;;;;;;;;;;;;

;; TODO: improve proof
(defrule heapp-of-tree-update.tree$-when-heapp
  (implies (heapp tree)
           (heapp (tree-update x val tree)))
  :induct t
  :enable (tree-update
           heap<-rules
           heap<-of-tree->head-when-heap<-all-l)
  :hints ('(:use ((:instance tree-update-hmax-heap-invariants
                             (a (tree-element->key (tree->head tree)))
                             (tree (tree->left tree)))
                  (:instance tree-update-hmax-heap-invariants
                             (a (tree-element->key (tree->head tree)))
                             (tree (tree->right tree))))))
  :prep-lemmas
  ((defruled tree-update-hmax-heap-invariants
     (implies (and (heapp tree)
                   (heap<-all-l tree a))
              (if (or (tree-empty-p tree)
                      (heap< (tree-element->key (tree->head tree)) x))
                  (and (equal (tree-element->key
                                (tree->head (tree-update x val tree)))
                              x)
                       (heap<-all-l (tree->left (tree-update x val tree))
                                    a)
                       (heap<-all-l (tree->right (tree-update x val tree))
                                    a))
                (heap<-all-l (tree-update x val tree) a)))
     :induct t
     :enable (tree-update
              heap<-all-l-extra-rules))))

;;;;;;;;;;;;;;;;;;;;

;; TODO
;; (defruled tree->head-of-tree-update
;;   (implies (and (bstp tree)
;;                 (heapp tree))
;;            (equal (tree->head (tree-update key val tree))
;;                   (if (or (tree-empty-p tree)
;;                           (heap< (tree-element->key (tree->head tree)) key))
;;                       (tree-element (hash key) key val)
;;                     (tree->head tree))))
;;   :induct t
;;   :enable (tree-update
;;            treeset::heap<-expensive-rules))

;; TODO
;; (defrule equal-of-tree-element->key-tree->head-of-tree-update-and-key
;;   (implies (heapp tree)
;;            (equal (equal (tree-element->key
;;                            (tree->head (tree-update key val tree)))
;;                          key)
;;                   (or (tree-empty-p tree)
;;                       (not (heap< key
;;                                   (tree-element->key (tree->head tree)))))))
;;   :enable (tree->head-of-tree-update
;;            heap<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-nodes-count-of-tree-update
  (implies (bstp tree)
           (equal (tree-nodes-count (tree-update key val tree))
                  (if (treeset::in key (tree-key-set tree))
                      (tree-nodes-count tree)
                    (+ 1 (tree-nodes-count tree)))))
  :induct t
  :enable (tree-update
           tree-nodes-count
           bstp
           data::<<-rules
           )
  ;; TODO: disable this rule by default?
  ;; Or, I think preferably, make non-definition.
  :disable tree-nodes-count-when-bstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-singleton
  (key
   (hash (unsigned-byte-p 32 hash))
   val)
  :guard (mbe :logic (equal (hash key) hash)
              :exec (data::u32-equal (hash key) hash))
  (mbe :logic (tree-update key val nil)
       :exec (tree-node (tree-element hash key val) nil nil))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           tree-update))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-update-with-hash
  (key
   (hash (unsigned-byte-p 32 hash))
   val
   (tree treep))
  :parents (implementation)
  :short "Add a key/value pair to the tree, given the key's hash."
  :long
  (xdoc::topstring
   (xdoc::p
     "Logically identical to @(tsee tree-update). In execution, the hash of
      @('key') is supplied by the caller instead of being computed at the
      insertion point. This is preferable when the hash is already known,
      e.g. because @('key') was taken from another tree."))
  :guard (mbe :logic (equal (hash key) hash)
              :exec (data::u32-equal (hash key) hash))
  (mbe :logic (tree-update key val tree)
       :exec
       (if (tree-empty-p tree)
           (tree-node (tree-element hash key val) nil nil)
         (let* ((head (tree->head tree))
                (head-key (tree-element->key head)))
           (cond ((equal key head-key)
                  (tree-node (tree-element hash key val)
                             (tree->left tree)
                             (tree->right tree)))
                 ((<< key head-key)
                  (let* ((left$ (tree-update-with-hash key
                                                       hash
                                                       val
                                                       (tree->left tree)))
                         (head-left$ (tree->head left$))
                         (tree$ (tree-node head
                                           left$
                                           (tree->right tree))))
                    (if (heap<-with-hashes
                          head-key
                          (tree-element->key head-left$)
                          (tree-element->hash head)
                          (tree-element->hash head-left$))
                        (rotate-right tree$)
                      tree$)))
                 (t
                  (let* ((right$ (tree-update-with-hash key
                                                        hash
                                                        val
                                                        (tree->right tree)))
                         (head-right$ (tree->head right$))
                         (tree$ (tree-node head
                                           (tree->left tree)
                                           right$)))
                    (if (heap<-with-hashes
                          head-key
                          (tree-element->key head-right$)
                          (tree-element->hash head)
                          (tree-element->hash head-right$))
                        (rotate-left tree$)
                      tree$)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           tree-update-with-hash)
                        :expand (tree-update key val tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-update
  ((key acl2-numberp)
   val
   (tree acl2-number-treep))
  (mbe :logic (tree-update key val tree)
       :exec
       (if (tree-empty-p tree)
           (tree-node (tree-element (acl2-number-hash key) key val) nil nil)
         (let* ((head (tree->head tree))
                (head-key (tree-element->key head)))
           (cond ((= key head-key)
                  (tree-node (tree-element (tree-element->hash head) key val)
                             (tree->left tree)
                             (tree->right tree)))
                 ((data::acl2-number-<< key head-key)
                  (let* ((left$ (acl2-number-tree-update key
                                                         val
                                                         (tree->left tree)))
                         (head-left$ (tree->head left$))
                         (tree$ (tree-node head
                                           left$
                                           (tree->right tree))))
                    (if (heap<-with-hashes
                          head-key
                          (tree-element->key head-left$)
                          (tree-element->hash head)
                          (tree-element->hash head-left$))
                        (rotate-right tree$)
                      tree$)))
                 (t
                  (let* ((right$ (acl2-number-tree-update key
                                                          val
                                                          (tree->right tree)))
                         (head-right$ (tree->head right$))
                         (tree$ (tree-node head
                                           (tree->left tree)
                                           right$)))
                    (if (heap<-with-hashes
                          head-key
                          (tree-element->key head-right$)
                          (tree-element->hash head)
                          (tree-element->hash head-right$))
                        (rotate-left tree$)
                      tree$)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable acl2-number-tree-update
                                           tree-keys-acl2-numberp)
                        :expand (tree-update key val tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-update
  ((key symbolp)
   val
   (tree symbol-treep))
  (mbe :logic (tree-update key val tree)
       :exec
       (if (tree-empty-p tree)
           (tree-node (tree-element (symbol-hash key) key val) nil nil)
         (let* ((head (tree->head tree))
                (head-key (tree-element->key head)))
           (cond ((eq key head-key)
                  (tree-node (tree-element (tree-element->hash head) key val)
                             (tree->left tree)
                             (tree->right tree)))
                 ((data::symbol-<< key head-key)
                  (let* ((left$ (symbol-tree-update key val (tree->left tree)))
                         (head-left$ (tree->head left$))
                         (tree$ (tree-node head
                                           left$
                                           (tree->right tree))))
                    (if (heap<-with-hashes
                          head-key
                          (tree-element->key head-left$)
                          (tree-element->hash head)
                          (tree-element->hash head-left$))
                        (rotate-right tree$)
                      tree$)))
                 (t
                  (let* ((right$ (symbol-tree-update key
                                                     val
                                                     (tree->right tree)))
                         (head-right$ (tree->head right$))
                         (tree$ (tree-node head
                                           (tree->left tree)
                                           right$)))
                    (if (heap<-with-hashes
                          head-key
                          (tree-element->key head-right$)
                          (tree-element->hash head)
                          (tree-element->hash head-right$))
                        (rotate-left tree$)
                      tree$)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable symbol-tree-update
                                           tree-keys-symbolp)
                        :expand (tree-update key val tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-update
  ((key eqlablep)
   val
   (tree eqlable-treep))
  (mbe :logic (tree-update key val tree)
       :exec
       (if (tree-empty-p tree)
           (tree-node (tree-element (eqlable-hash key) key val) nil nil)
         (let* ((head (tree->head tree))
                (head-key (tree-element->key head)))
           (cond ((eql key head-key)
                  (tree-node (tree-element (tree-element->hash head) key val)
                             (tree->left tree)
                             (tree->right tree)))
                 ((data::eqlable-<< key head-key)
                  (let* ((left$ (eqlable-tree-update key val (tree->left tree)))
                         (head-left$ (tree->head left$))
                         (tree$ (tree-node head
                                           left$
                                           (tree->right tree))))
                    (if (heap<-with-hashes
                          head-key
                          (tree-element->key head-left$)
                          (tree-element->hash head)
                          (tree-element->hash head-left$))
                        (rotate-right tree$)
                      tree$)))
                 (t
                  (let* ((right$ (eqlable-tree-update key
                                                      val
                                                      (tree->right tree)))
                         (head-right$ (tree->head right$))
                         (tree$ (tree-node head
                                           (tree->left tree)
                                           right$)))
                    (if (heap<-with-hashes
                          head-key
                          (tree-element->key head-right$)
                          (tree-element->hash head)
                          (tree-element->hash head-right$))
                        (rotate-left tree$)
                      tree$)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable eqlable-tree-update
                                           tree-keys-eqlablep)
                        :expand (tree-update key val tree))))
