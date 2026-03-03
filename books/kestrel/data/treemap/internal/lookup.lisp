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

(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/union-defs" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "heap-defs")
(include-book "keys-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "keys"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-lookup
  (key
   (tree treep))
  :parents (implementation)
  :short "Lookup a key in the tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "This function is defined to be as logically convenient as possible. For
     execution, @(tsee tree-search-lookup) is used instead."))
  (cond ((tree-empty-p tree)
         nil)
        ((equal key (tree-element->key (tree->head tree)))
         (tree-element->val (tree->head tree)))
        ((treeset::in key (tree-key-set (tree->left tree)))
         (tree-lookup key (tree->left tree)))
        (t
         (tree-lookup key (tree->right tree))))
  :guard-hints (("Goal" :in-theory (enable tree-element->key
                                           tree-element->val
                                           tree-empty-p
                                           tree->head
                                           tree-element-fix
                                           tree-element-p
                                           treep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-lookup)))

(defrule tree-lookup-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-lookup key tree0)
                  (tree-lookup key tree1)))
  :rule-classes :congruence
  :expand ((tree-lookup key tree0)
           (tree-lookup key tree1))
  :enable tree-equiv)

(defrule tree-lookup-of-tree-node
  (equal (tree-lookup key (tree-node head left right))
         (cond ((equal key (tree-element->key head))
                (tree-element->val head))
               ((treeset::in key (tree-key-set left))
                (tree-lookup key left))
               (t
                (tree-lookup key right))))
  :enable tree-lookup)

(defruled tree-lookup-when-tree-empty-p
  (implies (tree-empty-p tree)
           (not (tree-lookup key tree)))
  :enable tree-lookup)

(defrule tree-lookup-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (not (tree-lookup key tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-lookup-when-tree-empty-p)

(defrule tree-lookup-of-arg1-and-nil
  (not (tree-lookup key nil))
  :enable tree-lookup-when-tree-empty-p)

(defrule tree-lookup-of-tree->head
  (equal (tree-lookup (tree-element->key (tree->head tree)) tree)
         (if (tree-empty-p tree)
             nil
           (tree-element->val (tree->head tree)))))

(defruled in-of-tree-key-set-when-tree-lookup
  (implies (tree-lookup key tree)
           (treeset::in key (tree-key-set tree)))
  :induct t
  :enable tree-lookup)

(defrule in-of-tree-key-set-when-tree-lookup-type-prescription
  (implies (not (equal (tree-lookup key tree) nil))
           (treeset::in key (tree-key-set tree)))
  :rule-classes :type-prescription
  :use in-of-tree-key-set-when-tree-lookup)

(defrule in-of-tree-key-set-when-tree-lookup-forward-chaining
  (implies (tree-lookup key tree)
           (treeset::in key (tree-key-set tree)))
  :rule-classes :forward-chaining
  :by in-of-tree-key-set-when-tree-lookup)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-lookup-when-not-in-of-tree-key-set
  (implies (not (treeset::in key (tree-key-set tree)))
           (equal (tree-lookup key tree)
                  nil)))

;; (defrule tree-lookup-when-not-in-of-tree-key-set-type-prescription
;;   (implies (equal (treeset::in key (tree-key-set tree)) nil)
;;            (equal (tree-lookup key tree)
;;                   nil))
;;   :rule-classes :type-prescription
;;   :use tree-lookup-when-not-in-of-tree-key-set)
;;
;; (defrule tree-lookup-when-not-in-of-tree-key-set-forward-chaining
;;   (implies (not (treeset::in key (tree-key-set tree)))
;;            (equal (tree-lookup key tree)
;;                   nil))
;;   :rule-classes :forward-chaining
;;   :by tree-lookup-when-not-in-of-tree-key-set)

;; (defrule tree-lookup-when-not-in-of-tree-key-set-cheap
;;   (implies (not (treeset::in key (tree-key-set tree)))
;;            (equal (tree-lookup key tree)
;;                   nil))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :by tree-lookup-when-not-in-of-tree-key-set)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-lookup-when-<<-of-tree->head
  (implies (and (bstp tree)
                (<< (tree-element->key (tree->head tree)) key))
           (equal (tree-lookup key tree)
                  (tree-lookup key (tree->right tree))))
  :enable data::<<-rules)

(defrule tree-lookup-when->>-of-tree->head
  (implies (and (bstp tree)
                (<< key (tree-element->key (tree->head tree))))
           (equal (tree-lookup key tree)
                  (tree-lookup key (tree->left tree))))
  :enable (tree-lookup
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled tree-lookup-when-in-of-tree-key-set-tree->left-and-bstp
  (implies (and (treeset::in key (tree-key-set (tree->left tree)))
                (bstp tree))
           (equal (tree-lookup key tree)
                  (tree-lookup key (tree->left tree)))))

(defrule tree-lookup-when-in-of-tree-key-set-tree->left-and-bstp-cheap
  (implies (and (treeset::in key (tree-key-set (tree->left tree)))
                (bstp tree))
           (equal (tree-lookup key tree)
                  (tree-lookup key (tree->left tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :by tree-lookup-when-in-of-tree-key-set-tree->left-and-bstp)

(defruled tree-lookup-when-in-of-tree-key-set-tree->right-and-bstp
  (implies (and (treeset::in key (tree-key-set (tree->right tree)))
                (bstp tree))
           (equal (tree-lookup key tree)
                  (tree-lookup key (tree->right tree))))
  :enable tree-lookup)

(defrule tree-lookup-when-in-of-tree-key-set-tree->right-and-bstp-cheap
  (implies (and (treeset::in key (tree-key-set (tree->right tree)))
                (bstp tree))
           (equal (tree-lookup key tree)
                  (tree-lookup key (tree->right tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :by tree-lookup-when-in-of-tree-key-set-tree->right-and-bstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-search-assoc
  (key
   (tree treep))
  :parents (tree-lookup)
  :short "A performant variant of @(tsee tree-lookup) which uses a BST
          assumption."
  (if (tree-empty-p tree)
      nil
    (let ((head-key (tree-element->key (tree->head tree))))
      (cond ((equal key head-key)
             (mbe :logic (cons key (tree-element->val (tree->head tree)))
                  :exec (cdr (the cons (tree->head tree)))))
            ((<< key head-key)
             (tree-search-assoc key (tree->left tree)))
            (t
             (tree-search-assoc key (tree->right tree))))))
  :guard-hints (("Goal" :in-theory (enable tree-element->key
                                           tree-element->val
                                           tree-empty-p
                                           tree->head
                                           tree-element-p
                                           treep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-search-assoc)))

(defrule tree-search-assoc-type-prescription
  (or (consp (tree-search-assoc key tree))
      (equal (tree-search-assoc key tree) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-search-assoc)

(defrule tree-search-assoc-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-search-assoc key tree0)
                  (tree-search-assoc key tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-search-assoc)

(defruled in-of-tree-key-set-when-tree-search-assoc
  (implies (tree-search-assoc key tree)
           (treeset::in key (tree-key-set tree)))
  :induct t
  :enable (tree-search-assoc
           tree-key-set))

(defrule in-of-tree-key-set-when-tree-search-assoc-forward-chaining
  (implies (tree-search-assoc key tree)
           (treeset::in key (tree-key-set tree)))
  :rule-classes :forward-chaining
  :by in-of-tree-key-set-when-tree-search-assoc)

(defrule tree-search-assoc-becomes-tree-lookup-when-bstp
  (implies (bstp tree)
           (equal (tree-search-assoc key tree)
                  (if (treeset::in key (tree-key-set tree))
                      (cons key (tree-lookup key tree))
                    nil)))
  :rule-classes :definition
  :induct t
  :enable tree-search-assoc)

(defrule equal-of-tree-search-assoc-and-cons
  (equal (equal (tree-search-assoc key tree) (cons x y))
         (and (tree-search-assoc key tree)
              (equal x key)
              (equal (cdr (tree-search-assoc key tree)) y)))
  :induct t
  :enable tree-search-assoc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: equality variant versions
(define tree-search-lookup!
  (key
   (tree treep))
  :guard (tree-search-assoc key tree)
  :parents (tree-lookup)
  :short "A performant variant of @(tsee tree-search-assoc) which also assumes
          the key is in the tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "Only the value is returned."))
  (mbe :logic (cdr (tree-search-assoc key tree))
       :exec (let ((head-key (tree-element->key (tree->head tree))))
               (cond ((equal key head-key)
                      (tree-element->val (tree->head tree)))
                     ((<< key head-key)
                      (tree-search-lookup! key (tree->left tree)))
                     (t
                      (tree-search-lookup! key (tree->right tree))))))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-search-lookup!-becomes-exec
  (implies (tree-search-assoc key tree)
           (equal (tree-search-lookup! key tree)
                  (cond ((equal key (tree-element->key (tree->head tree)))
                         (tree-element->val (tree->head tree)))
                        ((<< key (tree-element->key (tree->head tree)))
                         (tree-search-lookup! key (tree->left tree)))
                        (t
                         (tree-search-lookup! key (tree->right tree))))))
  :enable (tree-search-lookup!
           tree-search-assoc))

(verify-guards tree-search-lookup!
  :hints (("Goal" :in-theory (enable tree-search-assoc
                                     tree-search-lookup!)
                  :use tree-search-lookup!-becomes-exec)))

(defrule tree-search-lookup!-becomes-tree-lookup-when-bstp
  (implies (bstp tree)
           (equal (tree-search-lookup! key tree)
                  (tree-lookup key tree)))
  :rule-classes :definition
  :enable tree-search-lookup!)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-search-assoc
  ((key acl2-numberp)
   (tree acl2-number-treep))
  (mbe :logic (tree-search-assoc key tree)
       :exec
       (if (tree-empty-p tree)
           nil
         (let ((head-key (tree-element->key (tree->head tree))))
           (cond ((= key head-key)
                  (cdr (the cons (tree->head tree))))
                 ((data::acl2-number-<< key head-key)
                  (acl2-number-tree-search-assoc key (tree->left tree)))
                 (t
                  (acl2-number-tree-search-assoc key (tree->right tree)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-search-assoc
                                           acl2-number-tree-search-assoc
                                           tree-keys-acl2-numberp
                                           tree-element->key
                                           tree-element->val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-search-assoc
  ((key symbolp)
   (tree symbol-treep))
  (mbe :logic (tree-search-assoc key tree)
       :exec
       (if (tree-empty-p tree)
           nil
         (let ((head-key (tree-element->key (tree->head tree))))
           (cond ((eq key head-key)
                  (cdr (the cons (tree->head tree))))
                 ((data::symbol-<< key head-key)
                  (symbol-tree-search-assoc key (tree->left tree)))
                 (t
                  (symbol-tree-search-assoc key (tree->right tree)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-search-assoc
                                           symbol-tree-search-assoc
                                           tree-keys-symbolp
                                           tree-element->key
                                           tree-element->val
                                           tree-empty-p
                                           tree->head
                                           tree-element-p
                                           treep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-search-assoc
  ((key eqlablep)
   (tree eqlable-treep))
  (mbe :logic (tree-search-assoc key tree)
       :exec
       (if (tree-empty-p tree)
           nil
         (let ((head-key (tree-element->key (tree->head tree))))
           (cond ((eql key head-key)
                  (cdr (the cons (tree->head tree))))
                 ((data::eqlable-<< key head-key)
                  (eqlable-tree-search-assoc key (tree->left tree)))
                 (t
                  (eqlable-tree-search-assoc key (tree->right tree)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-search-assoc
                                           eqlable-tree-search-assoc
                                           tree-keys-eqlablep
                                           tree-element->key
                                           tree-element->val
                                           tree-empty-p
                                           tree->head
                                           tree-element-p
                                           treep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy tree-lookup-extra-rules
  '(tree-lookup-when-tree-empty-p
    tree-lookup-when-not-in-of-tree-key-set
    tree-lookup-when-in-of-tree-key-set-tree->left-and-bstp
    tree-lookup-when-in-of-tree-key-set-tree->right-and-bstp
    ))
