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
   (hash (unsigned-byte-p 32 hash))
   (tree treep))
  :parents (implementation)
  :short "Insert a value into the tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "The element is inserted with respect to the binary search tree ordering
      and then rebalanced with respect to the @(tsee heapp) property."))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  :returns (mv (inp booleanp)
               (tree$ treep))
  (if (tree-empty-p tree)
      (mv nil
          (tree-node (tagged-element hash x) nil nil))
    (let* ((hash (mbe :logic (hash x) :exec hash))
           (head (tree->head tree))
           (head-elem (tagged-element->elem head)))
      (cond ((equal x head-elem)
             (mv t
                 (tree-fix tree)))
            ((<< x head-elem)
             (mv-let (inp left$)
                     (tree-insert x hash (tree->left tree))
               (if inp
                   (mv t (tree-fix tree))
                 (let ((head-left$ (tree->head left$))
                       (tree$ (tree-node head
                                         left$
                                         (tree->right tree))))
                   (mv nil
                       (if (heap<-with-hashes
                             head-elem
                             (tagged-element->elem head-left$)
                             (tagged-element->hash head)
                             (tagged-element->hash head-left$))
                           (rotate-right tree$)
                         tree$))))))
            (t
             (mv-let (inp right$)
                     (tree-insert x hash (tree->right tree))
               (if inp
                   (mv t (tree-fix tree))
                 (let ((head-right$ (tree->head right$))
                       (tree$ (tree-node head
                                         (tree->left tree)
                                         right$)))
                   (mv nil
                       (if (heap<-with-hashes
                             head-elem
                             (tagged-element->elem head-right$)
                             (tagged-element->hash head)
                             (tagged-element->hash head-right$))
                           (rotate-left tree$)
                         tree$)))))))))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-of-tree-insert.tree$
  (not (tree-empty-p (mv-nth 1 (tree-insert x hash tree))))
  :induct t
  :enable tree-insert)

(verify-guards tree-insert
  :hints (("Goal" :in-theory (enable data::u32-equal))))

(defrule tree-insert.tree$-type-prescription
  (consp (mv-nth 1 (tree-insert x hash tree)))
  :rule-classes :type-prescription
  :use tree-empty-p-of-tree-insert.tree$
  :enable tree-empty-p
  :disable tree-empty-p-of-tree-insert.tree$)

(defrule tree-insert-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-insert x hash tree0)
                  (tree-insert x hash tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-insert)

;; Logically, the second argument is ignored. We choose to arbitrarily
;; normalize it to nil.
(defruled tree-insert-arg2-becomes-nil
  (equal (tree-insert x hash tree)
         (tree-insert x nil tree))
  :induct t
  :enable tree-insert)

(defrule tree-insert-when-arg2-not-nil-syntaxp
  (implies (syntaxp (not (equal hash ''nil)))
           (equal (tree-insert x hash tree)
                  (tree-insert x nil tree)))
  :by tree-insert-arg2-becomes-nil)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-insert.inp
  (equal (mv-nth 0 (tree-insert x hash tree))
         (tree-search-in x tree))
  :induct t
  :enable (tree-insert
           tree-search-in))

(defruled tree-insert.tree$-when-tree-insert.inp
  (implies (mv-nth 0 (tree-insert x hash tree))
           (equal (mv-nth 1 (tree-insert x hash tree))
                  (tree-fix tree)))
  :induct t
  :enable (tree-insert
           tree-search-in))

(defrule tree-insert.tree$-when-tree-insert.inp-cheap
  (implies (mv-nth 0 (tree-insert x hash tree))
           (equal (mv-nth 1 (tree-insert x hash tree))
                  (tree-fix tree)))
  :by tree-insert.tree$-when-tree-insert.inp)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-tree-insert.tree$
  (equal (tree-in x (mv-nth 1 (tree-insert y hash tree)))
         (or (equal x y)
             (tree-in x tree)))
  :induct t
  :enable tree-insert)

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-insert.tree$
  (equal (<<-all-l (mv-nth 1 (tree-insert y hash tree)) x)
         (and (<< y x)
              (<<-all-l tree x)))
  :induct t
  :enable (<<-all-l
           tree-insert))

(defrule <<-all-r-of-tree-insert.tree$
  (equal (<<-all-r x (mv-nth 1 (tree-insert y hash tree)))
         (and (<< x y)
              (<<-all-r x tree)))
  :induct t
  :enable (<<-all-r
           tree-insert))

(defrule bst-of-tree-insert.tree$-when-bst
  (implies (bstp tree)
           (bstp (mv-nth 1 (tree-insert x hash tree))))
  :induct t
  :enable (tree-insert
           bstp
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-insert.tree$
  (equal (heap<-all-l (mv-nth 1 (tree-insert y hash tree)) x)
         (and (heap< y x)
              (heap<-all-l tree x)))
  :induct t
  :enable (heap<-all-l
           tree-insert))

;;;;;;;;;;;;;;;;;;;;

;; TODO: improve proof
(defrule heapp-of-tree-insert.tree$-when-heapp
  (implies (heapp tree)
           (heapp (mv-nth 1 (tree-insert x hash tree))))
  :induct t
  :enable (tree-insert
           heap<-rules
           heap<-of-tree->head-when-heap<-all-l)
  :hints ('(:use ((:instance tree-insert-hmax-heap-invariants
                             (a (tagged-element->elem (tree->head tree)))
                             (tree (tree->left tree)))
                  (:instance tree-insert-hmax-heap-invariants
                             (a (tagged-element->elem (tree->head tree)))
                             (tree (tree->right tree))))))
  :prep-lemmas
  ((defruled tree-insert-hmax-heap-invariants
     (implies (and (heapp tree)
                   (heap<-all-l tree a))
              (if (or (tree-empty-p tree)
                      (heap< (tagged-element->elem (tree->head tree)) x))
                  (and (equal (tagged-element->elem (tree->head (mv-nth 1 (tree-insert x hash tree))))
                              x)
                       (heap<-all-l (tree->left (mv-nth 1 (tree-insert x hash tree)))
                                    a)
                       (heap<-all-l (tree->right (mv-nth 1 (tree-insert x hash tree)))
                                    a))
                (heap<-all-l (mv-nth 1 (tree-insert x hash tree)) a)))
     :induct t
     :enable (tree-insert
              heapp
              heap<-all-l-extra-rules))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-nodes-count-of-tree-insert.tree$
  (implies (bstp tree)
           (equal (tree-nodes-count (mv-nth 1 (tree-insert x hash tree)))
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
           (equal (tree-min (mv-nth 1 (tree-insert x hash tree)))
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
                      (tree-insert x nil nil)
                (declare (ignore inp))
                tree)
       :exec (tree-node (tagged-element hash x) nil nil))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           tree-insert))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-insert
  ((x acl2-numberp)
   (hash (unsigned-byte-p 32 hash))
   (tree acl2-number-treep))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  (mbe :logic (tree-insert x hash tree)
       :exec
       (if (tree-empty-p tree)
           (mv nil
               (tree-node (tagged-element hash x) nil nil))
         (let* ((hash (mbe :logic (hash x) :exec hash))
                (head (tree->head tree))
                (head-elem (tagged-element->elem head)))
           (cond ((= x head-elem)
                  (mv t
                      (tree-fix tree)))
                 ((data::acl2-number-<< x head-elem)
                  (mv-let (inp left$)
                          (acl2-number-tree-insert x hash (tree->left tree))
                    (if inp
                        (mv t (tree-fix tree))
                      (let ((head-left$ (tree->head left$))
                            (tree$ (tree-node head
                                              left$
                                              (tree->right tree))))
                        (mv nil
                            (if (heap<-with-hashes
                                  head-elem
                                  (tagged-element->elem head-left$)
                                  (tagged-element->hash head)
                                  (tagged-element->hash head-left$))
                                (rotate-right tree$)
                              tree$))))))
                 (t
                  (mv-let (inp right$)
                          (acl2-number-tree-insert x hash (tree->right tree))
                    (if inp
                        (mv t (tree-fix tree))
                      (let ((head-right$ (tree->head right$))
                            (tree$ (tree-node head
                                              (tree->left tree)
                                              right$)))
                        (mv nil
                            (if (heap<-with-hashes
                                  head-elem
                                  (tagged-element->elem head-right$)
                                  (tagged-element->hash head)
                                  (tagged-element->hash head-right$))
                                (rotate-left tree$)
                              tree$))))))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           tree-insert
                                           acl2-number-tree-insert
                                           tree-all-acl2-numberp)
                        ;; TODO: avoid expand hint
                        :expand (tree-insert x nil tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-insert
  ((x symbolp)
   (hash (unsigned-byte-p 32 hash))
   (tree symbol-treep))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  (mbe :logic (tree-insert x hash tree)
       :exec
       (if (tree-empty-p tree)
           (mv nil
               (tree-node (tagged-element hash x) nil nil))
         (let* ((hash (mbe :logic (hash x) :exec hash))
                (head (tree->head tree))
                (head-elem (tagged-element->elem head)))
           (cond ((eq x head-elem)
                  (mv t
                      (tree-fix tree)))
                 ((data::symbol-<< x head-elem)
                  (mv-let (inp left$)
                          (symbol-tree-insert x hash (tree->left tree))
                    (if inp
                        (mv t (tree-fix tree))
                      (let ((head-left$ (tree->head left$))
                            (tree$ (tree-node head
                                              left$
                                              (tree->right tree))))
                        (mv nil
                            (if (heap<-with-hashes
                                  head-elem
                                  (tagged-element->elem head-left$)
                                  (tagged-element->hash head)
                                  (tagged-element->hash head-left$))
                                (rotate-right tree$)
                              tree$))))))
                 (t
                  (mv-let (inp right$)
                          (symbol-tree-insert x hash (tree->right tree))
                    (if inp
                        (mv t (tree-fix tree))
                      (let ((head-right$ (tree->head right$))
                            (tree$ (tree-node head
                                              (tree->left tree)
                                              right$)))
                        (mv nil
                            (if (heap<-with-hashes
                                  head-elem
                                  (tagged-element->elem head-right$)
                                  (tagged-element->hash head)
                                  (tagged-element->hash head-right$))
                                (rotate-left tree$)
                              tree$))))))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           tree-insert
                                           symbol-tree-insert
                                           tree-all-symbolp)
                        ;; TODO: avoid expand hint
                        :expand (tree-insert x nil tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-insert
  ((x eqlablep)
   (hash (unsigned-byte-p 32 hash))
   (tree eqlable-treep))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  (mbe :logic (tree-insert x hash tree)
       :exec
       (if (tree-empty-p tree)
           (mv nil
               (tree-node (tagged-element hash x) nil nil))
         (let* ((hash (mbe :logic (hash x) :exec hash))
                (head (tree->head tree))
                (head-elem (tagged-element->elem head)))
           (cond ((eql x head-elem)
                  (mv t
                      (tree-fix tree)))
                 ((data::eqlable-<< x head-elem)
                  (mv-let (inp left$)
                          (eqlable-tree-insert x hash (tree->left tree))
                    (if inp
                        (mv t (tree-fix tree))
                      (let ((head-left$ (tree->head left$))
                            (tree$ (tree-node head
                                              left$
                                              (tree->right tree))))
                        (mv nil
                            (if (heap<-with-hashes
                                  head-elem
                                  (tagged-element->elem head-left$)
                                  (tagged-element->hash head)
                                  (tagged-element->hash head-left$))
                                (rotate-right tree$)
                              tree$))))))
                 (t
                  (mv-let (inp right$)
                          (eqlable-tree-insert x hash (tree->right tree))
                    (if inp
                        (mv t (tree-fix tree))
                      (let ((head-right$ (tree->head right$))
                            (tree$ (tree-node head
                                              (tree->left tree)
                                              right$)))
                        (mv nil
                            (if (heap<-with-hashes
                                  head-elem
                                  (tagged-element->elem head-right$)
                                  (tagged-element->hash head)
                                  (tagged-element->hash head-right$))
                                (rotate-left tree$)
                              tree$))))))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           tree-insert
                                           eqlable-tree-insert
                                           tree-all-eqlablep)
                        ;; TODO: avoid expand hint
                        :expand (tree-insert x nil tree))))
