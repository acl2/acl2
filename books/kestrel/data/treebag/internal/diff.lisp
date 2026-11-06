; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEBAG")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/treeset/in-defs" :dir :system)

(include-book "kestrel/data/treemap/internal/tree-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/bst-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/heap-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/join-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/split-defs" :dir :system)

(include-book "map-values-all-posp-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/treeset/hash" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "kestrel/data/treemap/internal/tree" :dir :system))
(local (include-book "kestrel/data/treemap/internal/bst" :dir :system))
(local (include-book "kestrel/data/treemap/internal/heap" :dir :system))
(local (include-book "kestrel/data/treemap/internal/keys" :dir :system))
(local (include-book "kestrel/data/treemap/internal/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/internal/join" :dir :system))
(local (include-book "kestrel/data/treemap/internal/split" :dir :system))

(local (include-book "map-values-all-posp"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lower the value of each key of the first tree by its value in the second,
;; dropping the key when nothing remains. The tree whose head comes first in
;; heap order is the one kept on top: the other tree is split at that head's
;; key, and the halves are subtracted against the head's subtrees. A key of the
;; first tree which the second lacks keeps its node.

(define tree-diff ((x treemap::treep)
                   (y treemap::treep))
  :guard (and (tree-all-vals-posp x)
              (tree-all-vals-posp y))
  :returns (tree treemap::treep)
  (cond ((or (treemap::tree-empty-p x)
             (treemap::tree-empty-p y))
         (treemap::tree-fix x))
        ((treemap::heap<-with-tree-element (treemap::tree->head x)
                                           (treemap::tree->head y))
         (mv-let (assoc left right)
                 (treemap::tree-split
                   (treemap::tree-element->key (treemap::tree->head y))
                   x)
           (let ((left (tree-diff left (treemap::tree->left y)))
                 (right (tree-diff right (treemap::tree->right y))))
             (if (and assoc
                      (< (treemap::tree-element->val (treemap::tree->head y))
                         (cdr assoc)))
                 (treemap::tree-node
                   (treemap::tree-element
                     (treemap::tree-element->hash (treemap::tree->head y))
                     (treemap::tree-element->key (treemap::tree->head y))
                     (- (cdr assoc)
                        (treemap::tree-element->val (treemap::tree->head y))))
                   left
                   right)
               (mbe :logic (treemap::tree-join-at
                             (treemap::tree-element->key (treemap::tree->head y))
                             left
                             right)
                    :exec (treemap::tree-join left right))))))
        (t
         (mv-let (assoc left right)
                 (treemap::tree-split
                   (treemap::tree-element->key (treemap::tree->head x))
                   y)
           (let ((left (tree-diff (treemap::tree->left x) left))
                 (right (tree-diff (treemap::tree->right x) right)))
             (cond ((not assoc)
                    (treemap::tree-node-with-hint
                      (treemap::tree->head x) left right x))
                   ((< (cdr assoc)
                       (treemap::tree-element->val (treemap::tree->head x)))
                    (treemap::tree-node-with-hint
                      (treemap::tree-element
                        (treemap::tree-element->hash (treemap::tree->head x))
                        (treemap::tree-element->key (treemap::tree->head x))
                        (- (treemap::tree-element->val (treemap::tree->head x))
                           (cdr assoc)))
                      left
                      right
                      x))
                   (t
                    (mbe :logic (treemap::tree-join-at
                                  (treemap::tree-element->key
                                    (treemap::tree->head x))
                                  left
                                  right)
                         :exec (treemap::tree-join left right))))))))
  :measure (+ (acl2-count x)
              (acl2-count y))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable tree-all-vals-posp
                                           acl2::rationalp-when-posp
                                           acl2::acl2-numberp-when-posp
                                           treemap::tree-join-at))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-diff-when-tree-equiv-of-arg1-congruence
  (implies (treemap::tree-equiv x0 x1)
           (equal (tree-diff x0 y)
                  (tree-diff x1 y)))
  :rule-classes :congruence
  :induct t
  :enable tree-diff)

(defrule tree-diff-when-tree-equiv-of-arg2-congruence
  (implies (treemap::tree-equiv y0 y1)
           (equal (tree-diff x y0)
                  (tree-diff x y1)))
  :rule-classes :congruence
  :induct t
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree-key-set-of-tree-diff
  (implies (and (treemap::bstp x)
                (treemap::bstp y))
           (equal (treeset::in key (treemap::tree-key-set (tree-diff x y)))
                  (and (treeset::in key (treemap::tree-key-set x))
                       (or (not (treeset::in key (treemap::tree-key-set y)))
                           (< (treemap::tree-lookup key y)
                              (treemap::tree-lookup key x))))))
  :induct t
  :enable (tree-diff
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-diff
  (implies (treemap::<<-all-l x z)
           (treemap::<<-all-l (tree-diff x y) z))
  :induct t
  :enable tree-diff)

(defrule <<-all-r-of-arg1-and-tree-diff
  (implies (treemap::<<-all-r z x)
           (treemap::<<-all-r z (tree-diff x y)))
  :induct t
  :enable tree-diff)

(defrule bstp-of-tree-diff-when-bstp
  (implies (and (treemap::bstp x)
                (treemap::bstp y))
           (treemap::bstp (tree-diff x y)))
  :induct t
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-lookup-of-tree-diff
  (implies (and (treemap::bstp x)
                (treemap::bstp y))
           (equal (treemap::tree-lookup key (tree-diff x y))
                  (cond ((not (treeset::in key (treemap::tree-key-set x)))
                         nil)
                        ((not (treeset::in key (treemap::tree-key-set y)))
                         (treemap::tree-lookup key x))
                        ((< (treemap::tree-lookup key y)
                            (treemap::tree-lookup key x))
                         (- (treemap::tree-lookup key x)
                            (treemap::tree-lookup key y)))
                        (t nil))))
  :induct t
  :enable (tree-diff
           treemap::tree-lookup
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-diff
  (implies (treemap::heap<-all-l x z)
           (treemap::heap<-all-l (tree-diff x y) z))
  :induct t
  :enable tree-diff)

(defrule heapp-of-tree-diff-when-bstp-and-heapp
  (implies (and (treemap::bstp x)
                (treemap::bstp y)
                (treemap::heapp x)
                (treemap::heapp y))
           (treemap::heapp (tree-diff x y)))
  :induct t
  :hints ('(:cases ((equal (treemap::tree-element->key (treemap::tree->head x))
                           (treemap::tree-element->key (treemap::tree->head y))))))
  :enable (tree-diff
           treemap::heap<-all-l-extra-rules
           treemap::tree-split-extra-rules
           treemap::heap<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-all-vals-posp-of-tree-diff
  (implies (and (tree-all-vals-posp x)
                (tree-all-vals-posp y))
           (tree-all-vals-posp (tree-diff x y)))
  :induct t
  :enable (tree-diff
           tree-all-vals-posp
           posp
           acl2::integerp-when-posp
           acl2::acl2-numberp-when-posp))
