; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "../hash-defs")
(include-book "tree-defs")
(include-book "heap-order-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "../hash"))
(local (include-book "tree"))
(local (include-book "heap-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define heap<-with-tagged-element
  ((x tagged-element-p)
   (y tagged-element-p))
  (heap<-with-hashes (tagged-element->elem x)
                     (tagged-element->elem y)
                     (tagged-element->hash x)
                     (tagged-element->hash y))
  :enabled t
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define heap<-all-l
  ((tree treep)
   x)
  :parents (tree)
  :short "Check that all members of a tree are @(tsee heap<) some value."
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (tree-empty-p tree)
      (and (heap< (tagged-element->elem (tree->head tree)) x)
           (heap<-all-l (tree->left tree) x)
           (heap<-all-l (tree->right tree) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t heap<-all-l)))

(defrule heap<-all-l-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (heap<-all-l x a)
                  (heap<-all-l y a)))
  :rule-classes :congruence
  :expand ((heap<-all-l x a)
           (heap<-all-l y a))
  :enable tree-equiv)

(defrule heap<-all-l-of-nil
  (heap<-all-l nil tree)
  :enable heap<-all-l)

(defruled heap<-all-l-when-tree-empty-p
  (implies (tree-empty-p tree)
           (heap<-all-l tree x))
  :enable heap<-all-l)

(defrule heap<-all-l-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (heap<-all-l tree x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by heap<-all-l-when-tree-empty-p)

(defrule tree-empty-p-when-not-heap<-all-l-forward-chaining
  (implies (not (heap<-all-l tree x))
           (not (tree-empty-p tree)))
  :rule-classes :forward-chaining
  :enable heap<-all-l)

(defrule heap<-all-l-of-arg1-and-tree->head
  (equal (heap<-all-l tree (tagged-element->elem (tree->head tree)))
         (tree-empty-p tree))
  :enable (heap<-all-l
           heap<-rules))

(defruled heap<-all-l-of-tree->left-when-heap<-all-l
  (implies (heap<-all-l tree x)
           (heap<-all-l (tree->left tree) x))
  :enable heap<-all-l)

(defrule heap<-all-l-of-tree->left-when-heap<-all-l-cheap
  (implies (heap<-all-l tree x)
           (heap<-all-l (tree->left tree) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by heap<-all-l-of-tree->left-when-heap<-all-l)

(defruled heap<-all-l-of-tree->right-when-heap<-all-l
  (implies (heap<-all-l tree x)
           (heap<-all-l (tree->right tree) x))
  :enable heap<-all-l)

(defrule heap<-all-l-of-tree->right-when-heap<-all-l-cheap
  (implies (heap<-all-l tree x)
           (heap<-all-l (tree->right tree) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by heap<-all-l-of-tree->right-when-heap<-all-l)

(defrule heap<-all-l-of-tree-node
  (equal (heap<-all-l (tree-node head left right) x)
         (and (heap< (tagged-element->elem head) x)
              (heap<-all-l left x)
              (heap<-all-l right x)))
  :enable heap<-all-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled heap<-all-l-weaken
  (implies (and (heap< y x)
                (heap<-all-l tree y))
           (heap<-all-l tree x))
  :induct t
  :enable (heap<-all-l
           heap<-rules))

(defruled heap<-all-l-weaken2
  (implies (and (not (heap< x y))
                (heap<-all-l tree y))
           (heap<-all-l tree x))
  :enable heap<-all-l-weaken
  :use heap<-trichotomy)

;;;;;;;;;;;;;;;;;;;;

(defruled not-heap<-all-l-weaken
  (implies (and (heap< x y)
                (not (heap<-all-l tree y)))
           (not (heap<-all-l tree x)))
  :by heap<-all-l-weaken)

(defruled not-heap<-all-l-weaken2
  (implies (and (not (heap< y x))
                (not (heap<-all-l tree y)))
           (not (heap<-all-l tree x)))
  :by heap<-all-l-weaken2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled heap<-of-tree->head-when-heap<-all-l
  (implies (and (heap<-all-l tree x)
                (not (tree-empty-p tree)))
           (heap< (tagged-element->elem (tree->head tree)) x))
  :enable heap<-all-l)

(defrule heap<-of-tree->head-when-heap<-all-l-cheap
  (implies (and (heap<-all-l tree x)
                (not (tree-empty-p tree)))
           (heap< (tagged-element->elem (tree->head tree)) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :by heap<-of-tree->head-when-heap<-all-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fast-nonempty-heapp ((tree treep))
  :guard (not (tree-empty-p tree))
  :returns (mv (heapp booleanp :rule-classes :type-prescription)
               (hash-max (unsigned-byte-p 32 hash-max)))
  (let* ((head (tree->head tree))
         (hash-head (tagged-element->hash head)))
    (declare (type (unsigned-byte 32) hash-head))
    (if (tree-empty-p (tree->left tree))
        (if (tree-empty-p (tree->right tree))
            (mv t hash-head)
          (mv-let (heapp hash-right)
                  (fast-nonempty-heapp (tree->right tree))
            (declare (type (unsigned-byte 32) hash-right))
            (mv (and heapp
                     (heap<-with-hashes (tagged-element->elem
                                          (tree->head (tree->right tree)))
                                        (tagged-element->elem head)
                                        hash-right
                                        hash-head))
                hash-head)))
      (if (tree-empty-p (tree->right tree))
          (mv-let (heapp hash-left)
                  (fast-nonempty-heapp (tree->left tree))
            (declare (type (unsigned-byte 32) hash-left))
            (mv (and heapp
                     (heap<-with-hashes (tagged-element->elem
                                          (tree->head (tree->left tree)))
                                        (tagged-element->elem head)
                                        hash-left
                                        hash-head))
                hash-head))
        (mv-let (heapp hash-left)
                (fast-nonempty-heapp (tree->left tree))
          (declare (type (unsigned-byte 32) hash-left))
          (if heapp
              (mv-let (heapp hash-right)
                      (fast-nonempty-heapp (tree->right tree))
                (declare (type (unsigned-byte 32) hash-right))
                (mv (and heapp
                         (heap<-with-hashes (tagged-element->elem
                                              (tree->head (tree->left tree)))
                                            (tagged-element->elem head)
                                            hash-left
                                            hash-head)
                         (heap<-with-hashes (tagged-element->elem
                                              (tree->head (tree->right tree)))
                                            (tagged-element->elem head)
                                            hash-right
                                            hash-head))
                    hash-head))
            (mv nil hash-head))))))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defrule fast-nonempty-heapp-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (fast-nonempty-heapp tree0)
                  (fast-nonempty-heapp tree1)))
  :rule-classes :congruence
  :induct t
  :enable fast-nonempty-heapp)

(defrulel fast-nonempty-heapp.hash-max
  (equal (mv-nth 1 (fast-nonempty-heapp tree))
         (hash (tagged-element->elem (tree->head tree))))
  :expand (fast-nonempty-heapp tree))

(verify-guards fast-nonempty-heapp)

(defrulel fast-nonempty-heapp.heapp-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (mv-nth 0 (fast-nonempty-heapp tree))
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable fast-nonempty-heapp)

(defruledl fast-nonempty-heapp.heapp
  (equal (mv-nth 0 (fast-nonempty-heapp tree))
         (and (mv-nth 0 (fast-nonempty-heapp (tree->left tree)))
              (mv-nth 0 (fast-nonempty-heapp (tree->right tree)))
              (heap<-all-l (tree->left tree)
                           (tagged-element->elem (tree->head tree)))
              (heap<-all-l (tree->right tree)
                           (tagged-element->elem (tree->head tree)))))
  :induct t
  :enable (fast-nonempty-heapp
           heap<-all-l-weaken))

(defrulel fast-nonempty-heapp.heapp-when-not-tree-empty-p-cheap
  (implies (not (tree-empty-p tree))
           (equal (mv-nth 0 (fast-nonempty-heapp tree))
                  (and (mv-nth 0 (fast-nonempty-heapp (tree->left tree)))
                       (mv-nth 0 (fast-nonempty-heapp (tree->right tree)))
                       (heap<-all-l (tree->left tree)
                                    (tagged-element->elem (tree->head tree)))
                       (heap<-all-l (tree->right tree)
                                    (tagged-element->elem (tree->head tree))))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by fast-nonempty-heapp.heapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define heapp ((tree treep))
  (declare (xargs :type-prescription (booleanp (heapp tree))))
  :parents (tree)
  :short "Check the max heap property."
  (or (tree-empty-p tree)
      (mbe :logic (and (heapp (tree->left tree))
                       (heapp (tree->right tree))
                       (heap<-all-l (tree->left tree)
                                    (tagged-element->elem (tree->head tree)))
                       (heap<-all-l (tree->right tree)
                                    (tagged-element->elem (tree->head tree))))
           :exec (mv-let (heapp hash-max)
                         (fast-nonempty-heapp tree)
                   (declare (ignore hash-max))
                   heapp)))
  :inline t
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defruledl heapp-becomes-fast-nonempty-heapp
  (equal (heapp tree)
         (mv-nth 0 (fast-nonempty-heapp tree)))
  :induct t
  :enable heapp)

(verify-guards heapp$inline
  :hints (("Goal" :in-theory (enable heapp-becomes-fast-nonempty-heapp))))

;;;;;;;;;;;;;;;;;;;;

(defrule heapp-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (heapp tree0)
                  (heapp tree1)))
  :rule-classes :congruence
  :expand ((heapp tree0)
           (heapp tree1))
  :enable tree-equiv)

;;;;;;;;;;;;;;;;;;;;

(defruled heapp-of-tree->left-when-tree-orderdp
  (implies (heapp tree)
           (heapp (tree->left tree)))
  :enable heapp)

(defrule heapp-of-tree->left-when-tree-orderdp-cheap
  (implies (heapp tree)
           (heapp (tree->left tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by heapp-of-tree->left-when-tree-orderdp)

(defruled heapp-of-tree->right-when-heapp
  (implies (heapp tree)
           (heapp (tree->right tree)))
  :enable heapp)

(defrule heapp-of-tree->right-when-heapp-cheap
  (implies (heapp tree)
           (heapp (tree->right tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by heapp-of-tree->right-when-heapp)

;;;;;;;;;;;;;;;;;;;;

(defruled heapp-when-tree-empty-p
  (implies (tree-empty-p tree)
           (heapp tree))
  :enable heapp)

(defrule heapp-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (heapp tree))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by heapp-when-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;

(defruled heapp-when-not-tree-empty-p
  (implies (not (tree-empty-p tree))
           (equal (heapp tree)
                  (and (heapp (tree->left tree))
                       (heapp (tree->right tree))
                       (heap<-all-l (tree->left tree)
                                    (tagged-element->elem (tree->head tree)))
                       (heap<-all-l (tree->right tree)
                                    (tagged-element->elem (tree->head tree))))))
  :enable heapp)

(defrule heapp-when-not-tree-empty-p-cheap
  (implies (not (tree-empty-p tree))
           (equal (heapp tree)
                  (and (heapp (tree->left tree))
                       (heapp (tree->right tree))
                       (heap<-all-l (tree->left tree)
                                    (tagged-element->elem (tree->head tree)))
                       (heap<-all-l (tree->right tree)
                                    (tagged-element->elem (tree->head tree))))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by heapp-when-not-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-node
  (equal (heapp (tree-node head left right))
         (and (heapp left)
              (heapp right)
              (heap<-all-l left (tagged-element->elem head))
              (heap<-all-l right (tagged-element->elem head))))
  :enable heapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled heap<-of-tree->head-and-tree->head-of-tree->left
  (implies (and (heapp tree)
                (not (tree-empty-p (tree->left tree))))
           (heap< (tagged-element->elem (tree->head (tree->left tree)))
                  (tagged-element->elem (tree->head tree)))))

(defruled heap<-of-tree->head-and-tree->head-of-tree->right
  (implies (and (heapp tree)
                (not (tree-empty-p (tree->right tree))))
           (heap< (tagged-element->elem (tree->head (tree->right tree)))
                  (tagged-element->elem (tree->head tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy heap<-all-l-extra-rules
  '(heap<-all-l-when-tree-empty-p
    heap<-all-l-of-tree->left-when-heap<-all-l
    heap<-all-l-of-tree->right-when-heap<-all-l
    heap<-all-l-weaken
    heap<-all-l-weaken2
    not-heap<-all-l-weaken
    not-heap<-all-l-weaken2
    heap<-of-tree->head-when-heap<-all-l))

(defthy heapp-extra-rules
  '(heapp-of-tree->left-when-tree-orderdp
    heapp-of-tree->right-when-heapp
    heapp-when-tree-empty-p
    heapp-when-not-tree-empty-p
    heap<-of-tree->head-and-tree->head-of-tree->left
    heap<-of-tree->head-and-tree->head-of-tree->right))
