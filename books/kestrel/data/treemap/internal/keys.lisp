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

(include-book "kestrel/data/treeset/internal/tree-defs" :dir :system)
(include-book "kestrel/data/treeset/internal/bst-defs" :dir :system)
(include-book "kestrel/data/treeset/internal/heap-defs" :dir :system)
(include-book "kestrel/data/treeset/internal/in-defs" :dir :system)
(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/generic-typed-defs" :dir :system)
(include-book "kestrel/data/treeset/union-defs" :dir :system)
(include-book "kestrel/data/treeset/intersect-defs" :dir :system)
(include-book "kestrel/data/treeset/min-max-defs" :dir :system)

(include-book "kestrel/data/utilities/total-order/max-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/min-defs" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "heap-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/internal/tree" :dir :system))
(local (include-book "kestrel/data/treeset/internal/bst" :dir :system))
(local (include-book "kestrel/data/treeset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/treeset/internal/heap" :dir :system))
(local (include-book "kestrel/data/treeset/internal/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/internal/in" :dir :system))
(local (include-book "kestrel/data/treeset/hash" :dir :system))
(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/generic-typed" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/intersect" :dir :system))

(local (include-book "kestrel/data/utilities/total-order/max" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/min" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-key-set ((tree treep))
  :returns (set treeset::setp)
  (if (tree-empty-p tree)
      (treeset::empty)
    (treeset::insert-with-hash
      (tree-element->key (tree->head tree))
      (tree-element->hash (tree->head tree))
      (treeset::union (tree-key-set (tree->left tree))
                      (tree-key-set (tree->right tree)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

;; The executable rule is disabled because it often produces `nil` when it
;; should produce `emptyp`.
(in-theory (disable (:t tree-key-set) (:e tree-key-set)))

(defrule tree-key-set-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-key-set tree0)
                  (tree-key-set tree1)))
  :rule-classes :congruence
  :expand ((tree-key-set tree0)
           (tree-key-set tree1)))

(defrule bstp-of-tree-key-set
  (treeset::bstp (tree-key-set tree))
  :use setp-of-tree-key-set
  :enable treeset::break-abstraction
  :disable setp-of-tree-key-set)

(defrule emptyp-of-tree-key-set
  (equal (treeset::emptyp (tree-key-set tree))
         (tree-empty-p tree))
  :expand ((tree-key-set tree)))

(defruled tree-key-set-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree-key-set tree)
                  (treeset::empty)))
  :enable tree-key-set)

(defrule tree-key-set-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree-key-set tree)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-key-set-when-tree-empty-p)

(defrule tree-key-set-of-tree-node
  (equal (tree-key-set (tree-node head left right))
         (treeset::insert
           (tree-element->key head)
           (treeset::union (tree-key-set left)
                           (tree-key-set right))))
  :enable tree-key-set)

(defruled in-of-tree-key-set
  (equal (treeset::in key (tree-key-set tree))
         (and (not (tree-empty-p tree))
              (or (equal key (tree-element->key (tree->head tree)))
                  (treeset::in key (tree-key-set (tree->left tree)))
                  (treeset::in key (tree-key-set (tree->right tree))))))
  :enable tree-key-set)

(defruled in-of-tree-key-set-when-not-tree-empty-p
  (implies (not (tree-empty-p tree))
           (equal (treeset::in key (tree-key-set tree))
                  (or (equal key (tree-element->key (tree->head tree)))
                      (treeset::in key (tree-key-set (tree->left tree)))
                      (treeset::in key (tree-key-set (tree->right tree))))))
  :by in-of-tree-key-set)

(defrule in-of-tree-key-set-when-not-tree-empty-p-cheap
  (implies (not (tree-empty-p tree))
           (equal (treeset::in key (tree-key-set tree))
                  (or (equal key (tree-element->key (tree->head tree)))
                      (treeset::in key (tree-key-set (tree->left tree)))
                      (treeset::in key (tree-key-set (tree->right tree))))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by in-of-tree-key-set-when-not-tree-empty-p)

(defrule in-of-tree->head-and-tree-key-set
  (equal (treeset::in (tree-element->key (tree->head tree))
                      (tree-key-set tree))
         (not (tree-empty-p tree))))

;;;;;;;;;;;;;;;;;;;;

(defrule subset-of-tree-key-set-tree->left-and-tree-key-set
  (treeset::subset (tree-key-set (tree->left tree))
                   (tree-key-set tree))
  :expand ((tree-key-set tree))
  :enable treeset::pick-a-point-polar)

(defrule in-of-tree-key-set-when-in-of-tree-key-set-tree->left-forward-chaining
  (implies (treeset::in key (tree-key-set (tree->left tree)))
           (treeset::in key (tree-key-set tree)))
  :rule-classes :forward-chaining)

(defrule in-of-tree-key-set-tree->left-when-not-in-of-tree-key-set-cheap
  (implies (not (treeset::in key (tree-key-set tree)))
           (not (treeset::in key (tree-key-set (tree->left tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defrule subset-of-tree-key-set-tree->right-and-tree-key-set
  (treeset::subset (tree-key-set (tree->right tree))
                   (tree-key-set tree))
  :expand ((tree-key-set tree))
  :enable treeset::pick-a-point-polar)

(defrule in-of-tree-key-set-when-in-of-tree-key-set-tree->right-forward-chaining
  (implies (treeset::in key (tree-key-set (tree->right tree)))
           (treeset::in key (tree-key-set tree)))
  :rule-classes :forward-chaining)

(defrule in-of-tree-key-set-tree->right-when-not-in-of-tree-key-set-cheap
  (implies (not (treeset::in key (tree-key-set tree)))
           (not (treeset::in key (tree-key-set (tree->right tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;;;;;;;;;;;;;;;;;;;

(defruled in-of-tree-key-set-when-<<-all-r
  (implies (<<-all-r key tree)
           (not (treeset::in key (tree-key-set tree))))
  :induct t
  :enable (tree-key-set
           data::<<-rules))

(defrule in-of-tree-key-set-when-<<-all-r-forward-chaining
  (implies (<<-all-r key tree)
           (not (treeset::in key (tree-key-set tree))))
  :rule-classes :forward-chaining
  :by in-of-tree-key-set-when-<<-all-r)

(defruled in-of-tree-key-set-when-<<-all-l
  (implies (<<-all-l tree key)
           (not (treeset::in key (tree-key-set tree))))
  :induct t
  :enable (tree-key-set
           data::<<-rules))

(defrule in-of-tree-key-set-when-<<-all-l-forward-chaining
  (implies (<<-all-l tree key)
           (not (treeset::in key (tree-key-set tree))))
  :rule-classes :forward-chaining
  :by in-of-tree-key-set-when-<<-all-l)

;;;;;;;;;;;;;;;;;;;;

(defruled <<-when-<<-all-r-and-in-of-tree-key-set
  (implies (and (<<-all-r x tree)
                (treeset::in y (tree-key-set tree)))
           (<< x y))
  :induct t
  :enable tree-key-set)

(defrule <<-when-<<-all-r-and-in-of-tree-key-set-forward-chaining
  (implies (and (<<-all-r x tree)
                (treeset::in y (tree-key-set tree)))
           (<< x y))
  :rule-classes :forward-chaining
  :by <<-when-<<-all-r-and-in-of-tree-key-set)

(defruled <<-when-<<-all-l-and-in-of-tree-key-set
  (implies (and (<<-all-l tree y)
                (treeset::in x (tree-key-set tree)))
           (<< x y))
  :induct t
  :enable tree-key-set)

(defrule <<-when-<<-all-l-and-in-of-tree-key-set-forward-chaining
  (implies (and (<<-all-l tree y)
                (treeset::in x (tree-key-set tree)))
           (<< x y))
  :rule-classes :forward-chaining
  :by <<-when-<<-all-l-and-in-of-tree-key-set)

;;;;;;;;;;;;;;;;;;;;

;; TODO: remove the same hyp from treeset rule
(defrule in-of-tree-key-set-tree->right-when-not-<<-of-tree->head
  (implies (and (bstp tree)
                (not (<< (tree-element->key (tree->head tree)) key)))
           (not (treeset::in key (tree-key-set (tree->right tree))))))

;; TODO: remove the same hyp from treeset rule
(defrule in-of-tree-key-set-tree->right-when-not-<<-of-tree->head-weak
  (implies (and (bstp tree)
                (<< key (tree-element->key (tree->head tree))))
           (not (treeset::in key (tree-key-set (tree->right tree)))))
  :enable data::<<-rules)

;; TODO: remove the same hyp from treeset rule
(defrule in-of-tree-key-set-tree->left-when-not->>-of-tree->head
  (implies (and (bstp tree)
                (not (<< key (tree-element->key (tree->head tree)))))
           (not (treeset::in key (tree-key-set (tree->left tree))))))

;; TODO: remove the same hyp from treeset rule
(defrule in-of-tree-key-set-tree->left-when-not->>-of-tree->head-weak
  (implies (and (bstp tree)
                (<< (tree-element->key (tree->head tree)) key))
           (not (treeset::in key (tree-key-set (tree->left tree)))))
  :enable data::<<-rules)

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-when-heap-<-all-l-and-in-of-tree-key-set
  (implies (and (heap<-all-l tree x)
                (treeset::in key (tree-key-set tree)))
           (heap< key x))
  :induct t
  :enable (tree-key-set
           heap<-rules))

(defrule heap<-when-in-of-tree-key-set-and-heap-<-all-l
  (implies (and (treeset::in key (tree-key-set tree))
                (heap<-all-l tree x))
           (heap< key x))
  :by heap<-when-heap-<-all-l-and-in-of-tree-key-set)

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-of-tree->head-and-arg2-when-in-arg2-of-tree-key-set
  (implies (and (heapp tree)
                (treeset::in key (tree-key-set tree)))
           (not (heap< (tree-element->key (tree->head tree)) key)))
  :induct t
  :enable (tree-key-set
           heap<-rules))

(defrule heap<-of-arg1-and-tree->head-when-in-arg1-of-tree-key-set
  (implies (and (heapp tree)
                (treeset::in key (tree-key-set tree)))
           (equal (heap< key (tree-element->key (tree->head tree)))
                  (not (equal key (tree-element->key (tree->head tree))))))
  :use heap<-of-tree->head-and-arg2-when-in-arg2-of-tree-key-set
  :disable heap<-of-tree->head-and-arg2-when-in-arg2-of-tree-key-set)

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree->head-and-tree-key-set-tree->left
  (implies (bstp tree)
           (not (treeset::in (tree-element->key (tree->head tree))
                             (tree-key-set (tree->left tree))))))

(defrule in-of-tree->head-and-tree-key-set-tree->right
  (implies (bstp tree)
           (not (treeset::in (tree-element->key (tree->head tree))
                             (tree-key-set (tree->right tree))))))

;;;;;;;;;;;;;;;;;;;;

(defruled in-of-tree-key-set-tree->left-when-in-of-tree-key-set-tree->right
  (implies (and (bstp tree)
                (treeset::in key (tree-key-set (tree->right tree))))
           (not (treeset::in key (tree-key-set (tree->left tree)))))
  :use (in-of-tree-key-set-tree->right-when-not-<<-of-tree->head
        in-of-tree-key-set-tree->left-when-not->>-of-tree->head)
  :enable data::<<-rules)

(defrule in-of-tree-key-set-tree->left-when-in-of-tree-key-set-tree->right-forward-chaining
  (implies (and (treeset::in key (tree-key-set (tree->right tree)))
                (bstp tree))
           (not (treeset::in key (tree-key-set (tree->left tree)))))
  :rule-classes :forward-chaining
  :by in-of-tree-key-set-tree->left-when-in-of-tree-key-set-tree->right)

(defruled in-of-tree-set-tree-tree->right-when-in-of-tree-key-set-tree->left
  (implies (and (bstp tree)
                (treeset::in key (tree-key-set (tree->left tree))))
           (not (treeset::in key (tree-key-set (tree->right tree)))))
  :use (in-of-tree-key-set-tree->right-when-not-<<-of-tree->head
        in-of-tree-key-set-tree->left-when-not->>-of-tree->head)
  :enable data::<<-rules)

(defrule in-of-tree-set-tree-tree->right-when-in-of-tree-key-set-tree->left-forward-chaining
  (implies (and (treeset::in key (tree-key-set (tree->left tree)))
                (bstp tree))
           (not (treeset::in key (tree-key-set (tree->right tree)))))
  :rule-classes :forward-chaining
  :by in-of-tree-set-tree-tree->right-when-in-of-tree-key-set-tree->left)

;;;;;;;;;;;;;;;;;;;;

;; TODO: unused?
(defruled tree->head-when-heapp-and-in-of-tree->head
  (implies (and (heapp x)
                (heapp y)
                (treeset::in (tree-element->key (tree->head x))
                             (tree-key-set y))
                (treeset::in (tree-element->key (tree->head y))
                             (tree-key-set x)))
           (equal (tree-element->key (tree->head x))
                  (tree-element->key (tree->head y))))
  :use ((:instance heap<-of-arg1-and-tree->head-when-in-arg1-of-tree-key-set
                   (key (tree-element->key (tree->head x)))
                   (tree y)))
  :enable heap<-rules
  :disable heap<-of-arg1-and-tree->head-when-in-arg1-of-tree-key-set)

;; TODO: unused?
(defruled tree->head-when-heapp-and-in-of-tree->head-syntaxp
  (implies (and (treeset::in (tree-element->key (tree->head x))
                             (tree-key-set y))
                (syntaxp (<< y x))
                (heapp x)
                (heapp y)
                (treeset::in (tree-element->key (tree->head y))
                             (tree-key-set x)))
           (equal (tree-element->key (tree->head x))
                  (tree-element->key (tree->head y))))
  :by tree->head-when-heapp-and-in-of-tree->head)

;;;;;;;;;;;;;;;;;;;;

(defruled in-of-tree-key-set-right-when-disjoint-and-in-of-tree-key-set-left
  (implies (and (<<-all-l left x)
                (<<-all-r x right)
                (treeset::in y (tree-key-set left)))
           (not (treeset::in y (tree-key-set right))))
  :induct t
  :enable (tree-key-set
           data::<<-rules))

(defrule in-of-tree-key-set-right-when-disjoint-and-in-of-tree-key-set-left-forward-chaining
  (implies (and (<<-all-l left x)
                (<<-all-r x right)
                (treeset::in y (tree-key-set left)))
           (not (treeset::in y (tree-key-set right))))
  :rule-classes :forward-chaining
  :enable in-of-tree-key-set-right-when-disjoint-and-in-of-tree-key-set-left)

(defruled in-of-tree-key-set-left-when-disjoint-and-in-of-tree-key-set-right
  (implies (and (<<-all-l left x)
                (<<-all-r x right)
                (treeset::in y (tree-key-set right)))
           (not (treeset::in y (tree-key-set left))))
  :induct t
  :enable (tree-key-set
           data::<<-rules))

(defrule in-of-tree-key-set-left-when-disjoint-and-in-of-tree-key-set-right-forward-chaining
  (implies (and (<<-all-l left x)
                (<<-all-r x right)
                (treeset::in y (tree-key-set right)))
           (not (treeset::in y (tree-key-set left))))
  :rule-classes :forward-chaining
  :enable in-of-tree-key-set-left-when-disjoint-and-in-of-tree-key-set-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule intersect-of-tree-key-set-left-and-right
  (implies (bstp tree)
           (equal (treeset::intersect (tree-key-set (tree->left tree))
                                      (tree-key-set (tree->right tree)))
                  (treeset::empty)))
  :enable treeset::extensionality)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-key-tree ((tree treep))
  :returns (key-tree treeset::treep)
  (if (tree-empty-p tree)
      nil
    (treeset::tree-node (treeset::tree-element
                          (tree-element->hash (tree->head tree))
                          (tree-element->key (tree->head tree)))
                        (tree-key-tree (tree->left tree))
                        (tree-key-tree (tree->right tree))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-key-tree)))

(defrule tree-key-tree-type-prescription
  (or (consp (tree-key-tree tree))
      (equal (tree-key-tree tree) nil))
  :rule-classes (:type-prescription)
  :use treep-of-tree-key-tree)

(defrule tree-key-tree-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-key-tree tree0)
                  (tree-key-tree tree1)))
  :rule-classes :congruence
  :expand ((tree-key-tree tree0)
           (tree-key-tree tree1)))

(defrule tree-empty-p-of-tree-key-tree
  (equal (treeset::tree-empty-p (tree-key-tree tree))
         (tree-empty-p tree))
  :expand ((tree-key-tree tree)))

(defrule <<-all-l-of-tree-key-tree-when-<<-all-l
  (implies (<<-all-l tree x)
           (treeset::<<-all-l (tree-key-tree tree) x))
  :induct t
  :enable tree-key-tree)

(defrule <<-all-r-of-tree-key-tree-when-<<-all-r
  (implies (<<-all-r x tree)
           (treeset::<<-all-r x (tree-key-tree tree)))
  :induct t
  :enable tree-key-tree)

(defrule bstp-of-tree-key-tree-when-bstp
  (implies (bstp tree)
           (treeset::bstp (tree-key-tree tree)))
  :induct t
  :enable tree-key-tree)

(defrule heap<-all-l-of-tree-key-tree-when-<<-all-r
  (implies (heap<-all-l tree x)
           (treeset::heap<-all-l (tree-key-tree tree) x))
  :induct t
  :enable tree-key-tree)

(defrule heapp-of-tree-key-tree-when-heapp
  (implies (heapp tree)
           (treeset::heapp (tree-key-tree tree)))
  :induct t
  :enable tree-key-tree)

(defrule setp-of-tree-key-tree
  (implies (and (bstp tree)
                (heapp tree))
           (treeset::setp (tree-key-tree tree)))
  :enable treeset::setp)

(defruled tree-in-of-tree-key-tree
  (equal (treeset::tree-in key (tree-key-tree tree))
         (and (not (tree-empty-p tree))
              (or (equal key (tree-element->key (tree->head tree)))
                  (treeset::tree-in key (tree-key-tree (tree->left tree)))
                  (treeset::tree-in key (tree-key-tree (tree->right tree))))))
  :enable tree-key-tree)

(defruled tree-in-of-tree-key-tree-when-tree-empty-p
  (implies (tree-empty-p tree)
           (not (treeset::tree-in key (tree-key-tree tree))))
  :use tree-in-of-tree-key-tree)

(defrule tree-in-of-tree-key-tree-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (not (treeset::tree-in key (tree-key-tree tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-in-of-tree-key-tree-when-tree-empty-p)

(defruled tree-in-of-tree-key-tree-when-not-tree-empty-p
  (implies (not (tree-empty-p tree))
           (equal (treeset::tree-in key (tree-key-tree tree))
                  (or (equal key (tree-element->key (tree->head tree)))
                      (treeset::tree-in key (tree-key-tree (tree->left tree)))
                      (treeset::tree-in key (tree-key-tree (tree->right tree))))))
  :use tree-in-of-tree-key-tree)

(defrule tree-in-of-tree-key-tree-when-not-tree-empty-p-cheap
  (implies (not (tree-empty-p tree))
           (equal (treeset::tree-in key (tree-key-tree tree))
                  (or (equal key (tree-element->key (tree->head tree)))
                      (treeset::tree-in key (tree-key-tree (tree->left tree)))
                      (treeset::tree-in key (tree-key-tree (tree->right tree))))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-in-of-tree-key-tree-when-not-tree-empty-p)

(defrule in-of-tree-key-tree
  (implies (and (bstp tree)
                (heapp tree))
           (equal (treeset::in key (tree-key-tree tree))
                  (treeset::tree-in key (tree-key-tree tree))))
  :enable treeset::in)

(defrule tree-key-tree-becomes-tree-key-set
  (implies (and (bstp tree)
                (heapp tree))
           (equal (tree-key-tree tree)
                  (tree-key-set tree)))
  :induct t
  :enable (tree-key-set
            tree-key-tree-when-bstp-and-heapp)
  :prep-lemmas
  ((defrule tree-key-tree-when-bstp-and-heapp
     (implies (and (bstp tree)
                   (heapp tree))
              (equal (tree-key-tree tree)
                     (if (tree-empty-p tree)
                         (treeset::empty)
                       (treeset::insert-with-hash
                         (tree-element->key (tree->head tree))
                         (tree-element->hash (tree->head tree))
                         (treeset::union (tree-key-tree (tree->left tree))
                                         (tree-key-tree (tree->right tree)))))))
     :rule-classes :definition
     :enable treeset::extensionality-no-backchain-limit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled tree-leftmost-of-tree-key-tree
  (equal (treeset::tree-leftmost (tree-key-tree tree))
         (if (tree-empty-p (tree->left tree))
             (tree-element->key (tree->head tree))
           (treeset::tree-leftmost (tree-key-tree (tree->left tree)))))
  :enable (treeset::tree-leftmost
           tree-key-tree
           irr-tree-element
           treeset::empty))

(defruled tree-min-of-tree-key-set-when-tree-empty-p-tree->left
  (implies (and (tree-empty-p (tree->left tree))
                (bstp tree)
                (heapp tree))
           (equal (treeset::min (tree-key-set tree))
                  (tree-element->key (tree->head tree))))
  :use tree-leftmost-of-tree-key-tree
  :enable treeset::min)

(defrule tree-min-of-tree-key-set--when-tree-empty-p-tree->left-cheap
  (implies (and (tree-empty-p (tree->left tree))
                (bstp tree)
                (heapp tree))
           (equal (treeset::min (tree-key-set tree))
                  (tree-element->key (tree->head tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :by tree-min-of-tree-key-set-when-tree-empty-p-tree->left)

(defruled tree-min-of-tree-key-set-when-not-tree-empty-p-tree->left
  (implies (and (not (tree-empty-p (tree->left tree)))
                (bstp tree)
                (heapp tree))
           (equal (treeset::min (tree-key-set tree))
                  (treeset::min (tree-key-set (tree->left tree)))))
  :use tree-leftmost-of-tree-key-tree
  :enable treeset::min)

(defrule tree-min-of-tree-key-set-when-not-tree-empty-p-tree->left-cheap
  (implies (and (not (tree-empty-p (tree->left tree)))
                (bstp tree)
                (heapp tree))
           (equal (treeset::min (tree-key-set tree))
                  (treeset::min (tree-key-set (tree->left tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :by tree-min-of-tree-key-set-when-not-tree-empty-p-tree->left)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-rightmost-of-tree-key-tree
  (equal (treeset::tree-rightmost (tree-key-tree tree))
         (if (tree-empty-p (tree->right tree))
             (tree-element->key (tree->head tree))
           (treeset::tree-rightmost (tree-key-tree (tree->right tree)))))
  :enable (treeset::tree-rightmost
           tree-key-tree
           irr-tree-element
           treeset::empty))

(defruled tree-max-of-tree-key-set-when-tree-empty-p-tree->right
  (implies (and (tree-empty-p (tree->right tree))
                (bstp tree)
                (heapp tree))
           (equal (treeset::max (tree-key-set tree))
                  (tree-element->key (tree->head tree))))
  :use tree-rightmost-of-tree-key-tree
  :enable treeset::max)

(defrule tree-max-of-tree-key-set--when-tree-empty-p-tree->right-cheap
  (implies (and (tree-empty-p (tree->right tree))
                (bstp tree)
                (heapp tree))
           (equal (treeset::max (tree-key-set tree))
                  (tree-element->key (tree->head tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :by tree-max-of-tree-key-set-when-tree-empty-p-tree->right)

(defruled tree-max-of-tree-key-set-when-not-tree-empty-p-tree->right
  (implies (and (not (tree-empty-p (tree->right tree)))
                (bstp tree)
                (heapp tree))
           (equal (treeset::max (tree-key-set tree))
                  (treeset::max (tree-key-set (tree->right tree)))))
  :use tree-rightmost-of-tree-key-tree
  :enable treeset::max)

(defrule tree-max-of-tree-key-set-when-not-tree-empty-p-tree->right-cheap
  (implies (and (not (tree-empty-p (tree->right tree)))
                (bstp tree)
                (heapp tree))
           (equal (treeset::max (tree-key-set tree))
                  (treeset::max (tree-key-set (tree->right tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :by tree-max-of-tree-key-set-when-not-tree-empty-p-tree->right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-keys-acl2-numberp ((tree treep))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (mbe :logic (treeset::set-all-acl2-numberp (tree-key-set tree))
       :exec (or (tree-empty-p tree)
                 (and (acl2-numberp (tree-element->key (tree->head tree)))
                      (tree-keys-acl2-numberp (tree->left tree))
                      (tree-keys-acl2-numberp (tree->right tree)))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-keys-acl2-numberp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-keys-acl2-numberp)))

(defrule tree-keys-acl2-numberp-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-keys-acl2-numberp tree0)
                  (tree-keys-acl2-numberp tree1)))
  :rule-classes :congruence)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-keys-symbolp ((tree treep))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (mbe :logic (treeset::set-all-symbolp (tree-key-set tree))
       :exec (or (tree-empty-p tree)
                 (and (symbolp (tree-element->key (tree->head tree)))
                      (tree-keys-symbolp (tree->left tree))
                      (tree-keys-symbolp (tree->right tree)))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-keys-symbolp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-keys-symbolp)))

(defrule tree-keys-symbolp-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-keys-symbolp tree0)
                  (tree-keys-symbolp tree1)))
  :rule-classes :congruence)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-keys-eqlablep ((tree treep))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (mbe :logic (treeset::set-all-eqlablep (tree-key-set tree))
       :exec (or (tree-empty-p tree)
                 (and (eqlablep (tree-element->key (tree->head tree)))
                      (tree-keys-eqlablep (tree->left tree))
                      (tree-keys-eqlablep (tree->right tree)))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-keys-eqlablep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-keys-eqlablep)))

(defrule tree-keys-eqlablep-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-keys-eqlablep tree0)
                  (tree-keys-eqlablep tree1)))
  :rule-classes :congruence)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule genericp-of-tree->head-when-set-all-genericp
  (implies (and (treeset::set-all-genericp (tree-key-set tree))
                (not (tree-empty-p tree)))
           (treeset::genericp (tree-element->key (tree->head tree)))))

(defrule acl2-numberp-of-tree->head-when-set-all-acl2-numberp
  (implies (and (treeset::set-all-acl2-numberp (tree-key-set tree))
                (not (tree-empty-p tree)))
           (acl2-numberp (tree-element->key (tree->head tree))))
  :use (:functional-instance
         genericp-of-tree->head-when-set-all-genericp
         (treeset::genericp acl2-numberp)
         (treeset::set-all-genericp treeset::set-all-acl2-numberp))
  :enable treeset::set-all-acl2-numberp-alt-definition)

(defrule symbolp-of-tree->head-when-set-all-symbolp
  (implies (and (treeset::set-all-symbolp (tree-key-set tree))
                (not (tree-empty-p tree)))
           (symbolp (tree-element->key (tree->head tree))))
  :use (:functional-instance
         genericp-of-tree->head-when-set-all-genericp
         (treeset::genericp symbolp)
         (treeset::set-all-genericp treeset::set-all-symbolp))
  :enable treeset::set-all-symbolp-alt-definition)

(defrule eqlablep-of-tree->head-when-set-all-eqlablep
  (implies (and (treeset::set-all-eqlablep (tree-key-set tree))
                (not (tree-empty-p tree)))
           (eqlablep (tree-element->key (tree->head tree))))
  :use (:functional-instance
         genericp-of-tree->head-when-set-all-genericp
         (treeset::genericp eqlablep)
         (treeset::set-all-genericp treeset::set-all-eqlablep))
  :enable treeset::set-all-eqlablep-alt-definition)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: mbe-in some slightly more efficient functions which does the treep and
;; tree-keys checks simultaneously.

(define acl2-number-treep (x)
  (and (treep x)
       (tree-keys-acl2-numberp x))
  :enabled t)

(define symbol-treep (x)
  (and (treep x)
       (tree-keys-symbolp x))
  :enabled t)

(define eqlable-treep (x)
  (and (treep x)
       (tree-keys-eqlablep x))
  :enabled t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy tree-key-set-extra-rules
  '(tree-key-set-when-tree-empty-p
    in-of-tree-key-set-when-not-tree-empty-p
    in-of-tree-key-set-when-<<-all-r
    in-of-tree-key-set-when-<<-all-l
    <<-when-<<-all-r-and-in-of-tree-key-set
    <<-when-<<-all-l-and-in-of-tree-key-set
    tree->head-when-heapp-and-in-of-tree->head-syntaxp
    ))
