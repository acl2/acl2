; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TBAG")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/tset/in-defs" :dir :system)

(include-book "kestrel/data/tmap/internal/tree-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/bst-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/heap-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/lookup-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/join-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/split-defs" :dir :system)

(include-book "map-values-all-posp-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/tset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/tset/hash" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))

(local (include-book "kestrel/data/tmap/internal/tree" :dir :system))
(local (include-book "kestrel/data/tmap/internal/bst" :dir :system))
(local (include-book "kestrel/data/tmap/internal/heap" :dir :system))
(local (include-book "kestrel/data/tmap/internal/keys" :dir :system))
(local (include-book "kestrel/data/tmap/internal/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/internal/join" :dir :system))
(local (include-book "kestrel/data/tmap/internal/split" :dir :system))

(local (include-book "map-values-all-posp"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lower the value of each key of the first tree by its value in the second,
;; dropping the key when nothing remains. The tree whose head comes first in
;; heap order is the one kept on top: the other tree is split at that head's
;; key, and the halves are subtracted against the head's subtrees. A key of the
;; first tree which the second lacks keeps its node.

(define tree-diff ((x tmap::treep)
                   (y tmap::treep))
  :guard (and (tree-all-vals-posp x)
              (tree-all-vals-posp y))
  :returns (tree tmap::treep)
  (cond ((or (tmap::tree-empty-p x)
             (tmap::tree-empty-p y))
         (tmap::tree-fix x))
        ((tmap::heap<-with-tree-element (tmap::tree->head x)
                                        (tmap::tree->head y))
         (mv-let (assoc left right)
                 (tmap::tree-split
                   (tmap::tree-element->key (tmap::tree->head y))
                   x)
           (let ((left (tree-diff left (tmap::tree->left y)))
                 (right (tree-diff right (tmap::tree->right y))))
             (if (and assoc
                      (< (tmap::tree-element->val (tmap::tree->head y))
                         (cdr assoc)))
                 (tmap::tree-node
                   (tmap::tree-element
                     (tmap::tree-element->hash (tmap::tree->head y))
                     (tmap::tree-element->key (tmap::tree->head y))
                     (- (cdr assoc)
                        (tmap::tree-element->val (tmap::tree->head y))))
                   left
                   right)
               (mbe :logic (tmap::tree-join-at
                             (tmap::tree-element->key (tmap::tree->head y))
                             left
                             right)
                    :exec (tmap::tree-join left right))))))
        (t
         (mv-let (assoc left right)
                 (tmap::tree-split
                   (tmap::tree-element->key (tmap::tree->head x))
                   y)
           (let ((left (tree-diff (tmap::tree->left x) left))
                 (right (tree-diff (tmap::tree->right x) right)))
             (cond ((not assoc)
                    (tmap::tree-node-with-hint
                      (tmap::tree->head x) left right x))
                   ((< (cdr assoc)
                       (tmap::tree-element->val (tmap::tree->head x)))
                    (tmap::tree-node-with-hint
                      (tmap::tree-element
                        (tmap::tree-element->hash (tmap::tree->head x))
                        (tmap::tree-element->key (tmap::tree->head x))
                        (- (tmap::tree-element->val (tmap::tree->head x))
                           (cdr assoc)))
                      left
                      right
                      x))
                   (t
                    (mbe :logic (tmap::tree-join-at
                                  (tmap::tree-element->key
                                    (tmap::tree->head x))
                                  left
                                  right)
                         :exec (tmap::tree-join left right))))))))
  :measure (+ (acl2-count x)
              (acl2-count y))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable tree-all-vals-posp
                                           acl2::rationalp-when-posp
                                           acl2::acl2-numberp-when-posp
                                           tmap::tree-join-at))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-diff-when-tree-equiv-of-arg1-congruence
  (implies (tmap::tree-equiv x0 x1)
           (equal (tree-diff x0 y)
                  (tree-diff x1 y)))
  :rule-classes :congruence
  :induct t
  :enable tree-diff)

(defrule tree-diff-when-tree-equiv-of-arg2-congruence
  (implies (tmap::tree-equiv y0 y1)
           (equal (tree-diff x y0)
                  (tree-diff x y1)))
  :rule-classes :congruence
  :induct t
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree-key-set-of-tree-diff
  (implies (and (tmap::bstp x)
                (tmap::bstp y))
           (equal (tset::in key (tmap::tree-key-set (tree-diff x y)))
                  (and (tset::in key (tmap::tree-key-set x))
                       (or (not (tset::in key (tmap::tree-key-set y)))
                           (< (tmap::tree-lookup key y)
                              (tmap::tree-lookup key x))))))
  :induct t
  :enable (tree-diff
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-diff
  (implies (tmap::<<-all-l x z)
           (tmap::<<-all-l (tree-diff x y) z))
  :induct t
  :enable tree-diff)

(defrule <<-all-r-of-arg1-and-tree-diff
  (implies (tmap::<<-all-r z x)
           (tmap::<<-all-r z (tree-diff x y)))
  :induct t
  :enable tree-diff)

(defrule bstp-of-tree-diff-when-bstp
  (implies (and (tmap::bstp x)
                (tmap::bstp y))
           (tmap::bstp (tree-diff x y)))
  :induct t
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-lookup-of-tree-diff
  (implies (and (tmap::bstp x)
                (tmap::bstp y))
           (equal (tmap::tree-lookup key (tree-diff x y))
                  (cond ((not (tset::in key (tmap::tree-key-set x)))
                         nil)
                        ((not (tset::in key (tmap::tree-key-set y)))
                         (tmap::tree-lookup key x))
                        ((< (tmap::tree-lookup key y)
                            (tmap::tree-lookup key x))
                         (- (tmap::tree-lookup key x)
                            (tmap::tree-lookup key y)))
                        (t nil))))
  :induct t
  :enable (tree-diff
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-diff
  (implies (tmap::heap<-all-l x z)
           (tmap::heap<-all-l (tree-diff x y) z))
  :induct t
  :enable tree-diff)

(defrule heapp-of-tree-diff-when-bstp-and-heapp
  (implies (and (tmap::bstp x)
                (tmap::bstp y)
                (tmap::heapp x)
                (tmap::heapp y))
           (tmap::heapp (tree-diff x y)))
  :induct t
  :hints ('(:cases ((equal (tmap::tree-element->key (tmap::tree->head x))
                           (tmap::tree-element->key (tmap::tree->head y))))))
  :enable (tree-diff
           tmap::heap<-all-l-extra-rules
           tmap::tree-split-extra-rules
           tmap::heap<-rules))

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
