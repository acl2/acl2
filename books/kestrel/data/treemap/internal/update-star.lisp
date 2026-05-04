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

(include-book "kestrel/data/treeset/union-defs" :dir :system)

(include-book "tree-defs")
(include-book "keys-defs")
(include-book "update-defs")
(include-book "split-defs")
(include-book "submap-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/treeset/hash" :dir :system))
(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/generic-typed" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "keys"))
(local (include-book "lookup"))
(local (include-book "update"))
(local (include-book "split"))
(local (include-book "submap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-update*
  ((x treep)
   (y treep))
  :returns (tree treep)
  :parents (implementation)
  :short "Take the left-biased union of two treaps."
  :long
  (xdoc::topstring
   (xdoc::p
     "The result might not be the union if the input trees are not binary
      search trees."))
  (cond ((tree-empty-p x)
         (tree-fix y))
        ((tree-empty-p y)
         (tree-fix x))
        ((heap<-with-tree-element (tree->head x) (tree->head y))
         (mv-let (assoc left right)
                 (tree-split (tree-element->key (tree->head y)) x)
           (let ((head
                   (if assoc
                       (mbe :logic (tree-element
                                     (tree-element->hash (tree->head y))
                                     (tree-element->key (tree->head y))
                                     (cdr assoc))
                            :exec (cons (tree-element->hash (tree->head y))
                                        assoc))
                     (tree->head y))))
             (tree-node head
                        (tree-update* left (tree->left y))
                        (tree-update* right (tree->right y))))))
        (t
         (mv-let (assoc left right)
                 (tree-split (tree-element->key (tree->head x)) y)
           (declare (ignore assoc))
           (tree-node (tree->head x)
                      (tree-update* (tree->left x) left)
                      (tree-update* (tree->right x) right)))))
  :measure (+ (acl2-count x)
              (acl2-count y))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable tree-element
                                           tree-element-p))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-update*-type-prescription
  (or (consp (tree-update* x y))
      (equal (tree-update* x y) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-update*)

(defrule tree-update*-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv x0 x1)
           (equal (tree-update* x0 z)
                  (tree-update* x1 z)))
  :rule-classes :congruence
  :induct t
  :enable tree-update*)

(defrule tree-update*-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv y0 y1)
           (equal (tree-update* x y0)
                  (tree-update* x y1)))
  :rule-classes :congruence
  :induct t
  :enable tree-update*)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-of-tree-update*
  (equal (tree-empty-p (tree-update* x y))
         (and (tree-empty-p x)
              (tree-empty-p y)))
  :induct t
  :enable tree-update*)

(defruled in-of-tree-key-set-of-tree-update*
  (implies (and (bstp x)
                (bstp y))
           (equal (treeset::in a (tree-key-set (tree-update* x y)))
                  (treeset::in a (treeset::union (tree-key-set x)
                                                 (tree-key-set y)))))
  :induct t
  :enable (tree-update*
           data::<<-rules))

(defrule tree-key-set-of-tree-update*
  (implies (and (bstp x)
                (bstp y))
           (equal (tree-key-set (tree-update* x y))
                  (treeset::union (tree-key-set x)
                                  (tree-key-set y))))
  :enable (treeset::extensionality
           in-of-tree-key-set-of-tree-update*))

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-update*
  (equal (<<-all-l (tree-update* x y) z)
         (and (<<-all-l x z)
              (<<-all-l y z)))
  :induct t
  :enable (tree-update*
           tree-split-extra-rules
           acl2::equal-of-booleans-cheap))

(defrule <<-all-r-of-arg1-tree-update*
  (equal (<<-all-r x (tree-update* y z))
         (and (<<-all-r x y)
              (<<-all-r x z)))
  :induct t
  :enable (tree-update*
           tree-split-extra-rules
           acl2::equal-of-booleans-cheap))

;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-tree-update*-when-bstp
  (implies (and (bstp x)
                (bstp y))
           (bstp (tree-update* x y)))
  :induct t
  :enable tree-update*)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-lookup-of-tree-update*
  (implies (and (bstp x)
                (bstp y))
           (equal (tree-lookup a (tree-update* x y))
                  (if (treeset::in a (tree-key-set x))
                      (tree-lookup a x)
                    (tree-lookup a y))))
  :induct t
  :enable (tree-update*
           tree-lookup
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-update*
  (equal (heap<-all-l (tree-update* x y) z)
         (and (heap<-all-l x z)
              (heap<-all-l y z)))
  :induct t
  :enable (tree-update*
           tree-split-extra-rules
           acl2::equal-of-booleans-cheap))

;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-update*-when-heapp
  (implies (and (heapp x)
                (heapp y))
           (heapp (tree-update* x y)))
  :induct t
  :hints ('(:cases ((equal (tree-element->key (tree->head x))
                           (tree-element->key (tree->head y))))))
  :enable (tree-update*
           heap<-all-l-extra-rules
           tree-split-extra-rules
           heap<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-update*
  ((x acl2-number-treep)
   (y acl2-number-treep))
  (mbe :logic (tree-update* x y)
       :exec
       (cond ((tree-empty-p x)
              y)
             ((tree-empty-p y)
              x)
             ((heap<-with-tree-element (tree->head x) (tree->head y))
              (mv-let (assoc left right)
                      (acl2-number-tree-split
                        (tree-element->key (tree->head y)) x)
                (let ((head
                        (if assoc
                            (mbe :logic (tree-element
                                          (tree-element->hash (tree->head y))
                                          (tree-element->key (tree->head y))
                                          (cdr assoc))
                                 :exec (cons (tree-element->hash (tree->head y))
                                             assoc))
                          (tree->head y))))
                  (tree-node head
                             (acl2-number-tree-update* left (tree->left y))
                             (acl2-number-tree-update* right (tree->right y))))))
             (t
              (mv-let (assoc left right)
                      (acl2-number-tree-split
                        (tree-element->key (tree->head x)) y)
                (declare (ignore assoc))
                (tree-node (tree->head x)
                           (acl2-number-tree-update* (tree->left x) left)
                           (acl2-number-tree-update* (tree->right x) right))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-update*
                                           acl2-number-tree-update*
                                           tree-element
                                           tree-element-p
                                           tree-keys-acl2-numberp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-update*
  ((x symbol-treep)
   (y symbol-treep))
  (mbe :logic (tree-update* x y)
       :exec
       (cond ((tree-empty-p x)
              y)
             ((tree-empty-p y)
              x)
             ((heap<-with-tree-element (tree->head x) (tree->head y))
              (mv-let (assoc left right)
                      (symbol-tree-split (tree-element->key (tree->head y)) x)
                (let ((head
                        (if assoc
                            (mbe :logic (tree-element
                                          (tree-element->hash (tree->head y))
                                          (tree-element->key (tree->head y))
                                          (cdr assoc))
                                 :exec (cons (tree-element->hash (tree->head y))
                                             assoc))
                          (tree->head y))))
                  (tree-node head
                             (symbol-tree-update* left (tree->left y))
                             (symbol-tree-update* right (tree->right y))))))
             (t
              (mv-let (assoc left right)
                      (symbol-tree-split (tree-element->key (tree->head x)) y)
                (declare (ignore assoc))
                (tree-node (tree->head x)
                           (symbol-tree-update* (tree->left x) left)
                           (symbol-tree-update* (tree->right x) right))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-update*
                                           symbol-tree-update*
                                           tree-element
                                           tree-element-p
                                           tree-keys-symbolp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-update*
  ((x eqlable-treep)
   (y eqlable-treep))
  (mbe :logic (tree-update* x y)
       :exec
       (cond ((tree-empty-p x)
              y)
             ((tree-empty-p y)
              x)
             ((heap<-with-tree-element (tree->head x) (tree->head y))
              (mv-let (assoc left right)
                      (eqlable-tree-split (tree-element->key (tree->head y)) x)
                (let ((head
                        (if assoc
                            (mbe :logic (tree-element
                                          (tree-element->hash (tree->head y))
                                          (tree-element->key (tree->head y))
                                          (cdr assoc))
                                 :exec (cons (tree-element->hash (tree->head y))
                                             assoc))
                          (tree->head y))))
                  (tree-node head
                             (eqlable-tree-update* left (tree->left y))
                             (eqlable-tree-update* right (tree->right y))))))
             (t
              (mv-let (assoc left right)
                      (eqlable-tree-split (tree-element->key (tree->head x)) y)
                (declare (ignore assoc))
                (tree-node (tree->head x)
                           (eqlable-tree-update* (tree->left x) left)
                           (eqlable-tree-update* (tree->right x) right))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-update*
                                           eqlable-tree-update*
                                           tree-element
                                           tree-element-p
                                           tree-keys-eqlablep))))
