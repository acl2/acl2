; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "../hash-defs")
(include-book "tree-defs")
(include-book "rotate-defs")
(include-book "count-defs")
(include-book "in-defs")
(include-book "min-max-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/fixed-size-words/u32" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/min" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "../hash"))
(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "heap-order"))
(local (include-book "count"))
(local (include-book "rotate"))
(local (include-book "in"))
(local (include-book "min-max"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-insert
  (x
   (tree treep))
  :parents (implementation)
  :short "Insert a value into the tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "The element is inserted with respect to the binary search tree ordering
      and then rebalanced with respect to the @(tsee heapp) property.")
   (xdoc::p
     "The hash of @('x') is computed lazily, only once the insertion point has
      been found. In particular, if @('x') is already present in the tree, it
      is never hashed. The rebalancing on the way back up compares the hashes
      stored in the nodes, so no further hashing is required. See @(tsee
      tree-insert-with-hash) for a variant which accepts a precomputed
      hash."))
  :returns (mv (inp booleanp)
               (tree$ treep))
  (if (tree-empty-p tree)
      (mv nil
          (tree-node (tree-element (hash x) x) nil nil))
    (let* ((head (tree->head tree))
           (head-elem (tree-element->val head)))
      (cond ((equal x head-elem)
             (mv t
                 (tree-fix tree)))
            ((<< x head-elem)
             (mv-let (inp left$)
                     (tree-insert x (tree->left tree))
               (if inp
                   (mv t (tree-fix tree))
                 (let ((head-left$ (tree->head left$))
                       (tree$ (tree-node head
                                         left$
                                         (tree->right tree))))
                   (mv nil
                       (if (heap<-with-hashes
                             head-elem
                             (tree-element->val head-left$)
                             (tree-element->hash head)
                             (tree-element->hash head-left$))
                           (rotate-right tree$)
                         tree$))))))
            (t
             (mv-let (inp right$)
                     (tree-insert x (tree->right tree))
               (if inp
                   (mv t (tree-fix tree))
                 (let ((head-right$ (tree->head right$))
                       (tree$ (tree-node head
                                         (tree->left tree)
                                         right$)))
                   (mv nil
                       (if (heap<-with-hashes
                             head-elem
                             (tree-element->val head-right$)
                             (tree-element->hash head)
                             (tree-element->hash head-right$))
                           (rotate-left tree$)
                         tree$)))))))))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-of-tree-insert.tree$
  (not (tree-empty-p (mv-nth 1 (tree-insert x tree))))
  :induct t
  :enable tree-insert)

(verify-guards tree-insert)

(defrule tree-insert.tree$-type-prescription
  (consp (mv-nth 1 (tree-insert x tree)))
  :rule-classes :type-prescription
  :use tree-empty-p-of-tree-insert.tree$
  :enable tree-empty-p
  :disable tree-empty-p-of-tree-insert.tree$)

(defrule tree-insert-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-insert x tree0)
                  (tree-insert x tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-insert)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-insert.inp
  (equal (mv-nth 0 (tree-insert x tree))
         (tree-search-in x tree))
  :induct t
  :enable (tree-insert
           tree-search-in))

(defruled tree-insert.tree$-when-tree-insert.inp
  (implies (mv-nth 0 (tree-insert x tree))
           (equal (mv-nth 1 (tree-insert x tree))
                  (tree-fix tree)))
  :induct t
  :enable (tree-insert
           tree-search-in))

(defrule tree-insert.tree$-when-tree-insert.inp-cheap
  (implies (mv-nth 0 (tree-insert x tree))
           (equal (mv-nth 1 (tree-insert x tree))
                  (tree-fix tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-insert.tree$-when-tree-insert.inp)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-tree-insert.tree$
  (equal (tree-in x (mv-nth 1 (tree-insert y tree)))
         (or (equal x y)
             (tree-in x tree)))
  :induct t
  :enable tree-insert)

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-insert.tree$
  (equal (<<-all-l (mv-nth 1 (tree-insert y tree)) x)
         (and (<< y x)
              (<<-all-l tree x)))
  :induct t
  :enable (<<-all-l
           tree-insert))

(defrule <<-all-r-of-tree-insert.tree$
  (equal (<<-all-r x (mv-nth 1 (tree-insert y tree)))
         (and (<< x y)
              (<<-all-r x tree)))
  :induct t
  :enable (<<-all-r
           tree-insert))

(defrule bstp-of-tree-insert.tree$-when-bstp
  (implies (bstp tree)
           (bstp (mv-nth 1 (tree-insert x tree))))
  :induct t
  :enable (tree-insert
           bstp
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-insert.tree$
  (equal (heap<-all-l (mv-nth 1 (tree-insert y tree)) x)
         (and (heap< y x)
              (heap<-all-l tree x)))
  :induct t
  :enable (heap<-all-l
           tree-insert))

;;;;;;;;;;;;;;;;;;;;

;; TODO: improve proof
(defrule heapp-of-tree-insert.tree$-when-heapp
  (implies (heapp tree)
           (heapp (mv-nth 1 (tree-insert x tree))))
  :induct t
  :enable (tree-insert
           heap<-rules
           heap<-of-tree->head-when-heap<-all-l)
  :hints ('(:use ((:instance tree-insert-hmax-heap-invariants
                             (a (tree-element->val (tree->head tree)))
                             (tree (tree->left tree)))
                  (:instance tree-insert-hmax-heap-invariants
                             (a (tree-element->val (tree->head tree)))
                             (tree (tree->right tree))))))
  :prep-lemmas
  ((defruled tree-insert-hmax-heap-invariants
     (implies (and (heapp tree)
                   (heap<-all-l tree a))
              (if (or (tree-empty-p tree)
                      (heap< (tree-element->val (tree->head tree)) x))
                  (and (equal (tree-element->val (tree->head (mv-nth 1 (tree-insert x tree))))
                              x)
                       (heap<-all-l (tree->left (mv-nth 1 (tree-insert x tree)))
                                    a)
                       (heap<-all-l (tree->right (mv-nth 1 (tree-insert x tree)))
                                    a))
                (heap<-all-l (mv-nth 1 (tree-insert x tree)) a)))
     :induct t
     :enable (tree-insert
              heapp
              heap<-all-l-extra-rules))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-nodes-count-of-tree-insert.tree$
  (implies (bstp tree)
           (equal (tree-nodes-count (mv-nth 1 (tree-insert x tree)))
                  (if (tree-in x tree)
                      (tree-nodes-count tree)
                    (+ 1 (tree-nodes-count tree)))))
  :induct t
  :enable (tree-insert
           tree-nodes-count
           bstp
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defruled tree-min-of-tree-insert-when-<<-all-r
  (implies (<<-all-r x tree)
           (equal (tree-min (mv-nth 1 (tree-insert x tree)))
                  x))
  :induct t
  :enable tree-insert)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-singleton
  (x
   (hash (unsigned-byte-p 32 hash)))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  (mbe :logic (mv-let (inp tree)
                      (tree-insert x nil)
                (declare (ignore inp))
                tree)
       :exec (tree-node (tree-element hash x) nil nil))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           tree-insert))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-insert-with-hash
  (x
   (hash (unsigned-byte-p 32 hash))
   (tree treep))
  :parents (implementation)
  :short "Insert a value into the tree, given its hash."
  :long
  (xdoc::topstring
   (xdoc::p
     "Logically identical to @(tsee tree-insert). In execution, the hash of
      @('x') is supplied by the caller instead of being computed at the
      insertion point. This is preferable when the hash is already known,
      e.g. because @('x') was taken from another tree."))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  (mbe :logic (tree-insert x tree)
       :exec
       (if (tree-empty-p tree)
           (mv nil
               (tree-node (tree-element hash x) nil nil))
         (let* ((head (tree->head tree))
                (head-elem (tree-element->val head)))
           (cond ((equal x head-elem)
                  (mv t
                      (tree-fix tree)))
                 ((<< x head-elem)
                  (mv-let (inp left$)
                          (tree-insert-with-hash x hash (tree->left tree))
                    (if inp
                        (mv t (tree-fix tree))
                      (let ((head-left$ (tree->head left$))
                            (tree$ (tree-node head
                                              left$
                                              (tree->right tree))))
                        (mv nil
                            (if (heap<-with-hashes
                                  head-elem
                                  (tree-element->val head-left$)
                                  (tree-element->hash head)
                                  (tree-element->hash head-left$))
                                (rotate-right tree$)
                              tree$))))))
                 (t
                  (mv-let (inp right$)
                          (tree-insert-with-hash x hash (tree->right tree))
                    (if inp
                        (mv t (tree-fix tree))
                      (let ((head-right$ (tree->head right$))
                            (tree$ (tree-node head
                                              (tree->left tree)
                                              right$)))
                        (mv nil
                            (if (heap<-with-hashes
                                  head-elem
                                  (tree-element->val head-right$)
                                  (tree-element->hash head)
                                  (tree-element->hash head-right$))
                                (rotate-left tree$)
                              tree$))))))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           tree-insert
                                           tree-insert-with-hash)
                        ;; TODO: avoid expand hint
                        :expand (tree-insert x tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-insert
  ((x acl2-numberp)
   (tree acl2-number-treep))
  (mbe :logic (tree-insert x tree)
       :exec
       (if (tree-empty-p tree)
           (mv nil
               (tree-node (tree-element (acl2-number-hash x) x) nil nil))
         (let* ((head (tree->head tree))
                (head-elem (tree-element->val head)))
           (cond ((= x head-elem)
                  (mv t
                      (tree-fix tree)))
                 ((data::acl2-number-<< x head-elem)
                  (mv-let (inp left$)
                          (acl2-number-tree-insert x (tree->left tree))
                    (if inp
                        (mv t (tree-fix tree))
                      (let ((head-left$ (tree->head left$))
                            (tree$ (tree-node head
                                              left$
                                              (tree->right tree))))
                        (mv nil
                            (if (heap<-with-hashes
                                  head-elem
                                  (tree-element->val head-left$)
                                  (tree-element->hash head)
                                  (tree-element->hash head-left$))
                                (rotate-right tree$)
                              tree$))))))
                 (t
                  (mv-let (inp right$)
                          (acl2-number-tree-insert x (tree->right tree))
                    (if inp
                        (mv t (tree-fix tree))
                      (let ((head-right$ (tree->head right$))
                            (tree$ (tree-node head
                                              (tree->left tree)
                                              right$)))
                        (mv nil
                            (if (heap<-with-hashes
                                  head-elem
                                  (tree-element->val head-right$)
                                  (tree-element->hash head)
                                  (tree-element->hash head-right$))
                                (rotate-left tree$)
                              tree$))))))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-insert
                                           acl2-number-tree-insert
                                           tree-all-acl2-numberp)
                        ;; TODO: avoid expand hint
                        :expand (tree-insert x tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-insert
  ((x symbolp)
   (tree symbol-treep))
  (mbe :logic (tree-insert x tree)
       :exec
       (if (tree-empty-p tree)
           (mv nil
               (tree-node (tree-element (symbol-hash x) x) nil nil))
         (let* ((head (tree->head tree))
                (head-elem (tree-element->val head)))
           (cond ((eq x head-elem)
                  (mv t
                      (tree-fix tree)))
                 ((data::symbol-<< x head-elem)
                  (mv-let (inp left$)
                          (symbol-tree-insert x (tree->left tree))
                    (if inp
                        (mv t (tree-fix tree))
                      (let ((head-left$ (tree->head left$))
                            (tree$ (tree-node head
                                              left$
                                              (tree->right tree))))
                        (mv nil
                            (if (heap<-with-hashes
                                  head-elem
                                  (tree-element->val head-left$)
                                  (tree-element->hash head)
                                  (tree-element->hash head-left$))
                                (rotate-right tree$)
                              tree$))))))
                 (t
                  (mv-let (inp right$)
                          (symbol-tree-insert x (tree->right tree))
                    (if inp
                        (mv t (tree-fix tree))
                      (let ((head-right$ (tree->head right$))
                            (tree$ (tree-node head
                                              (tree->left tree)
                                              right$)))
                        (mv nil
                            (if (heap<-with-hashes
                                  head-elem
                                  (tree-element->val head-right$)
                                  (tree-element->hash head)
                                  (tree-element->hash head-right$))
                                (rotate-left tree$)
                              tree$))))))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-insert
                                           symbol-tree-insert
                                           tree-all-symbolp)
                        ;; TODO: avoid expand hint
                        :expand (tree-insert x tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-insert
  ((x eqlablep)
   (tree eqlable-treep))
  (mbe :logic (tree-insert x tree)
       :exec
       (if (tree-empty-p tree)
           (mv nil
               (tree-node (tree-element (eqlable-hash x) x) nil nil))
         (let* ((head (tree->head tree))
                (head-elem (tree-element->val head)))
           (cond ((eql x head-elem)
                  (mv t
                      (tree-fix tree)))
                 ((data::eqlable-<< x head-elem)
                  (mv-let (inp left$)
                          (eqlable-tree-insert x (tree->left tree))
                    (if inp
                        (mv t (tree-fix tree))
                      (let ((head-left$ (tree->head left$))
                            (tree$ (tree-node head
                                              left$
                                              (tree->right tree))))
                        (mv nil
                            (if (heap<-with-hashes
                                  head-elem
                                  (tree-element->val head-left$)
                                  (tree-element->hash head)
                                  (tree-element->hash head-left$))
                                (rotate-right tree$)
                              tree$))))))
                 (t
                  (mv-let (inp right$)
                          (eqlable-tree-insert x (tree->right tree))
                    (if inp
                        (mv t (tree-fix tree))
                      (let ((head-right$ (tree->head right$))
                            (tree$ (tree-node head
                                              (tree->left tree)
                                              right$)))
                        (mv nil
                            (if (heap<-with-hashes
                                  head-elem
                                  (tree-element->val head-right$)
                                  (tree-element->hash head)
                                  (tree-element->hash head-right$))
                                (rotate-left tree$)
                              tree$))))))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-insert
                                           eqlable-tree-insert
                                           tree-all-eqlablep)
                        ;; TODO: avoid expand hint
                        :expand (tree-insert x tree))))
