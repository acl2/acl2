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

(include-book "kestrel/data/utilities/total-order/max-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/min-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/total-order/max" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/min" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-min ((tree treep))
  (if (tree-empty-p tree)
      nil
    (if (tree-empty-p (tree->left tree))
        (if (tree-empty-p (tree->right tree))
            (tagged-element->elem (tree->head tree))
          (min-<< (tagged-element->elem (tree->head tree))
                  (tree-min (tree->right tree))))
      (if (tree-empty-p (tree->right tree))
          (min-<< (tagged-element->elem (tree->head tree))
                  (tree-min (tree->left tree)))
        (min-<< (tagged-element->elem (tree->head tree))
                (tree-min (tree->left tree))
                (tree-min (tree->right tree)))))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-min-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-min tree0)
                  (tree-min tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-min)

(defruled tree-min-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree-min tree)
                  nil))
  :enable tree-min)

(defrule tree-min-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree-min tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-min-when-tree-empty-p)

(defrule tree-min-of-tree-node
  (equal (tree-min (tree-node head left right))
         (if (tree-empty-p left)
             (if (tree-empty-p right)
                 (tagged-element->elem head)
               (min-<< (tagged-element->elem head)
                       (tree-min right)))
           (if (tree-empty-p right)
               (min-<< (tagged-element->elem head)
                       (tree-min left))
             (min-<< (tagged-element->elem head)
                     (tree-min left)
                     (tree-min right)))))
  :enable tree-min)

(defrule tree-in-of-tree-min
  (equal (tree-in (tree-min tree) tree)
         (not (tree-empty-p tree)))
  :induct t
  :enable (tree-min
           tree-in
           min-<<))

(defruled <<-all-r-when-<<-of-arg1-and-tree-min
  (implies (<< a (tree-min tree))
           (<<-all-r a tree))
  :induct t
  :enable (tree-min
           <<-all-r))

(defrule <<-all-r-when-<<-of-arg1-and-tree-min-cheap
  (implies (<< a (tree-min tree))
           (<<-all-r a tree))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by <<-all-r-when-<<-of-arg1-and-tree-min)

(defrule <<-of-arg1-and-tree-min-when-not-tree-empty-p
  (implies (not (tree-empty-p tree))
           (equal (<< a (tree-min tree))
                  (<<-all-r a tree)))
  :induct t
  :enable (tree-min
           <<-all-r))

(defrule <<-of-arg1-and-tree-min-when-tree-in
  (implies (tree-in x tree)
           (not (<< x (tree-min tree))))
  :induct t
  :enable (tree-min
           tree-in
           data::<<-rules))

(defrule <<-of-tree-min-when-tree-in
  (implies (tree-in x tree)
           (equal (<< (tree-min tree) x)
                  (not (equal (tree-min tree) x))))
  :enable (data::<<-rules
           acl2::equal-of-booleans-cheap))

;;;;;;;;;;;;;;;;;;;;

;; TODO: improve proof
(defrule tree-min-when-bstp-definition
  (implies (bstp tree)
           (equal (tree-min tree)
                  (cond ((tree-empty-p tree)
                         nil)
                        ((tree-empty-p (tree->left tree))
                         (tagged-element->elem (tree->head tree)))
                        (t
                         (tree-min (tree->left tree))))))
  :rule-classes :definition
  :induct t
  :enable (tree-min
           data::<<-rules
           min-<<
           <<-all-r-weaken)
  :disable bstp-when-not-tree-empty-p-cheap
  :prep-lemmas
  ((defrule lemma0
     (implies (and (not (tree-empty-p (tree->left (tree->left tree))))
                   (<<-all-l (tree->left tree)
                             (tagged-element->elem (tree->head tree)))
                   (<<-all-r (tagged-element->elem (tree->head tree))
                             (tree->right tree)))
              (<<-all-r (tree-min (tree->left tree))
                        (tree->right tree)))
     :use ((:instance <<-all-r-weaken
                      (x (tree-min (tree->left tree)))
                      (y (tagged-element->elem (tree->head tree)))
                      (tree (tree->right tree))))
     :enable <<-when-<<-all-l-and-tree-in)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-max ((tree treep))
  (if (tree-empty-p tree)
      nil
    (if (tree-empty-p (tree->left tree))
        (if (tree-empty-p (tree->right tree))
            (tagged-element->elem (tree->head tree))
          (max-<< (tagged-element->elem (tree->head tree))
                  (tree-max (tree->right tree))))
      (if (tree-empty-p (tree->right tree))
          (max-<< (tagged-element->elem (tree->head tree))
                  (tree-max (tree->left tree)))
        (max-<< (tagged-element->elem (tree->head tree))
                (tree-max (tree->left tree))
                (tree-max (tree->right tree)))))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-max-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-max tree0)
                  (tree-max tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-max)

(defruled tree-max-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree-max tree)
                  nil))
  :enable tree-max)

(defrule tree-max-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree-max tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-max-when-tree-empty-p)

(defrule tree-in-of-tree-max
  (equal (tree-in (tree-max tree) tree)
         (not (tree-empty-p tree)))
  :induct t
  :enable (tree-max
           tree-in
           max-<<))

(defruled <<-all-l-when-<<-of-tree-max
  (implies (<< (tree-max tree) a)
           (<<-all-l tree a))
  :induct t
  :enable (tree-max
           <<-all-l))

(defrule <<-all-l-when-<<-of-tree-max-cheap
  (implies (<< (tree-max tree) a)
           (<<-all-l tree a))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by <<-all-l-when-<<-of-tree-max)

(defrule <<-of-tree-max-when-not-tree-empty-p
  (implies (not (tree-empty-p tree))
           (equal (<< (tree-max tree) a)
                  (<<-all-l tree a)))
  :induct t
  :enable (tree-max
           <<-all-l))

(defrule <<-of-tree-max-when-tree-in
  (implies (tree-in x tree)
           (not (<< (tree-max tree) x)))
  :induct t
  :enable (tree-max
           tree-in
           data::<<-rules))

(defrule <<-of-arg1-and-tree-max-when-tree-in
  (implies (tree-in x tree)
           (equal (<< x (tree-max tree))
                  (not (equal (tree-max tree) x))))
  :enable (data::<<-rules
           acl2::equal-of-booleans-cheap))

;;;;;;;;;;;;;;;;;;;;

;; TODO: improve proof
(defrule tree-max-when-bstp-definition
  (implies (bstp tree)
           (equal (tree-max tree)
                  (cond ((tree-empty-p tree)
                         nil)
                        ((tree-empty-p (tree->right tree))
                         (tagged-element->elem (tree->head tree)))
                        (t
                         (tree-max (tree->right tree))))))
  :rule-classes :definition
  :induct t
  :enable (tree-max
           data::<<-rules
           max-<<
           <<-all-l-weaken)
  :disable bstp-when-not-tree-empty-p-cheap)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-leftmost ((tree treep))
  :guard (not (tree-empty-p tree))
  (if (tree-empty-p (tree->left tree))
      (tagged-element->elem (tree->head tree))
    (tree-leftmost (tree->left tree))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-leftmost-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-leftmost tree0)
                  (tree-leftmost tree1)))
  :rule-classes :congruence
  :expand ((tree-leftmost tree0)
           (tree-leftmost tree1)))

(defruled tree-leftmost-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree-leftmost tree)
                  nil))
  :enable (tree-leftmost
           irr-tagged-element))

(defrule tree-leftmost-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree-leftmost tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-leftmost-when-tree-empty-p)

(defrule in-of-tree-leftmost-when-not-tree-empty-p
  (equal (tree-in (tree-leftmost tree) tree)
         (not (tree-empty-p tree)))
  :induct t
  :enable (tree-leftmost
           tree-in))

(defrule <<-of-tree-leftmost-when-<<-all-l
  (implies (and (<<-all-l tree x)
                (not (tree-empty-p tree)))
           (<< (tree-leftmost tree) x))
  :enable <<-when-<<-all-l-and-tree-in)

(defrule <<-of-arg1-and-tree-leftmost-when-<<-all-r
  (implies (and (<<-all-r x tree)
                (not (tree-empty-p tree)))
           (<< x (tree-leftmost tree)))
  :enable <<-when-<<-all-r-and-tree-in)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-leftmost-when-bstp
  (implies (bstp tree)
           (equal (tree-leftmost tree)
                  (tree-min tree)))
  :induct t
  :enable (tree-leftmost
           irr-tagged-element))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-rightmost ((tree treep))
  :guard (not (tree-empty-p tree))
  (if (tree-empty-p (tree->right tree))
      (tagged-element->elem (tree->head tree))
    (tree-rightmost (tree->right tree))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-rightmost-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-rightmost tree0)
                  (tree-rightmost tree1)))
  :rule-classes :congruence
  :expand ((tree-rightmost tree0)
           (tree-rightmost tree1)))

(defruled tree-rightmost-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree-rightmost tree)
                  nil))
  :enable (tree-rightmost
           irr-tagged-element))

(defrule tree-rightmost-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree-rightmost tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-rightmost-when-tree-empty-p)

(defrule in-of-tree-rightmost-when-not-tree-empty-p
  (equal (tree-in (tree-rightmost tree) tree)
         (not (tree-empty-p tree)))
  :induct t
  :enable (tree-rightmost
           tree-in))

(defrule <<-of-tree-rightmost-when-<<-all-l
  (implies (and (<<-all-l tree x)
                (not (tree-empty-p tree)))
           (<< (tree-rightmost tree) x))
  :enable <<-when-<<-all-l-and-tree-in)

(defrule <<-of-arg1-and-tree-rightmost-when-<<-all-r
  (implies (and (<<-all-r x tree)
                (not (tree-empty-p tree)))
           (<< x (tree-rightmost tree)))
  :enable <<-when-<<-all-r-and-tree-in)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-rightmost-when-bstp
  (implies (bstp tree)
           (equal (tree-rightmost tree)
                  (tree-max tree)))
  :induct t
  :enable (tree-rightmost
           irr-tagged-element))
