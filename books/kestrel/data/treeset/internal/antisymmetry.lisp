; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "tree-defs")
(include-book "in-defs")
(include-book "subset-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap-order"))
(local (include-book "heap"))
(local (include-book "in"))
(local (include-book "subset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: refactor to a less manual proof
(defrulel tree->head-when-tree-subset-p-tree-subset-p
  (implies (and (tree-subset-p x y)
                (syntaxp (<< y x))
                (tree-subset-p y x)
                (heapp x)
                (heapp y))
           (equal (tagged-element->elem (tree->head x))
                  (tagged-element->elem (tree->head y))))
  :disable (heap<-of-tree->head-and-arg2-when-tree-in-of-arg2
            tree-in-when-tree-in-and-tree-subset-p
            ;; TODO: why does this rule sabotage the proof?
            tree-subset-p-when-not-tree-in-of-tree->head-cheap)
  :use ((:instance heap<-of-tree->head-and-arg2-when-tree-in-of-arg2
                   (x (tagged-element->elem (tree->head x)))
                   (tree y))
        (:instance heap<-of-tree->head-and-arg2-when-tree-in-of-arg2
                   (x (tagged-element->elem (tree->head y)))
                   (tree x))
        (:instance tree-in-when-tree-in-and-tree-subset-p
                   (a (tagged-element->elem (tree->head x))))
        (:instance tree-in-when-tree-in-and-tree-subset-p
                   (a (tagged-element->elem (tree->head y)))
                   (x y)
                   (y x)))
  :cases ((tree-empty-p x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Clean up this pair

(defruledl equal-when-treep
  (implies (and (treep x)
                (treep y))
           (equal (equal x y)
                  (if (tree-empty-p x)
                      (tree-empty-p y)
                    (and (not (tree-empty-p y))
                         (equal (tagged-element->elem (tree->head x))
                                (tagged-element->elem (tree->head y)))
                         (equal (tree->left x)
                                (tree->left y))
                         (equal (tree->right x)
                                (tree->right y))))))
  :enable (treep
           tree-empty-p
           tree->head
           tree->left
           tree->right))

;; (defruledl equal-when-setp
;;   (implies (and (syntaxp (atom x))
;;                 (setp x)
;;                 (setp y)
;;                 (syntaxp (atom y)))
;;            (equal (equal x y)
;;                   (if (emptyp x)
;;                       (emptyp y)
;;                     (and (not (emptyp y))
;;                          (equal (head x)
;;                                 (head y))
;;                          (equal (left x)
;;                                 (left y))
;;                          (equal (right x)
;;                                 (right y))))))
;;   :enable (setp
;;            emptyp
;;            head
;;            left
;;            right
;;            treep
;;            tree-empty-p
;;            tree->head
;;            tree->left
;;            tree->right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-tree->left-when-tree-in-and-<<-all
  (implies (and (<<-all-r (tagged-element->elem (tree->head y))
                          (tree->right y))
                (<<-all-l (tree->left x)
                          (tagged-element->elem (tree->head y)))
                (tree-in a (tree->left x))
                (tree-in a y))
           (tree-in a (tree->left y)))
  :enable (tree-in
           data::<<-rules)
  :disable <<-when-<<-all-l-and-tree-in-forward-chaining
  :use ((:instance <<-when-<<-all-l-and-tree-in
                   (x a)
                   (y (tagged-element->elem (tree->head y)))
                   (tree (tree->left x)))))

(defrule tree-in-of-tree->left-when-tree-in-of-tree->left-of-tree-subset-p-and-<<-all-l
  (implies (and (tree-subset-p x y)
                (bstp y)
                (<<-all-l (tree->left x)
                          (tagged-element->elem (tree->head y)))
                (tree-in a (tree->left x)))
           (tree-in a (tree->left y)))
  :use tree-in-when-tree-in-and-tree-subset-p
  :disable tree-in-when-tree-in-and-tree-subset-p)

(defrule tree-subset-p-of-tree->left-tree->left-when-tree-subset-p-and-<<-all-l
  (implies (and (tree-subset-p x y)
                (bstp y)
                (<<-all-l (tree->left x)
                          (tagged-element->elem (tree->head y))))
           (tree-subset-p (tree->left x) (tree->left y)))
  ;; TODO: polarity based rewriting from tree-subset-p to sk when using
  ;; pick-a-point strategy?
  :use (:instance tree-subset-p-becomes-tree-subset-p-sk
                  (x (tree->left x))
                  (y (tree->left y)))
  :enable tree-subset-p-sk)

(defrule tree-subset-p-of-tree->left-tree->left-when-tree-subset-p-and-equal-tree->head-tree->head
  (implies (and (tree-subset-p x y)
                (bstp x)
                (bstp y)
                (equal (tagged-element->elem (tree->head x))
                       (tagged-element->elem (tree->head y))))
           (tree-subset-p (tree->left x) (tree->left y)))
  :disable tree-subset-p-of-tree->left-tree->left-when-tree-subset-p-and-<<-all-l
  :use tree-subset-p-of-tree->left-tree->left-when-tree-subset-p-and-<<-all-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO GJ: same as changes for left above

(defrule tree-in-of-tree->right-when-tree-in-and-<<-all
  (implies (and (<<-all-l (tree->left y)
                          (tagged-element->elem (tree->head y)))
                (<<-all-r (tagged-element->elem (tree->head y))
                          (tree->right x))
                (tree-in a (tree->right x))
                (tree-in a y))
           (tree-in a (tree->right y)))
  :enable (tree-in
           data::<<-rules)
  :disable <<-when-<<-all-r-and-tree-in-forward-chaining
  :use ((:instance <<-when-<<-all-r-and-tree-in
                   (x (tagged-element->elem (tree->head y)))
                   (y a)
                   (tree (tree->right x)))))

(defrule tree-in-of-right-when-tree-in-of-tree->right-of-tree-subset-p-and-<<-all-r
  (implies (and (tree-subset-p x y)
                (bstp y)
                (<<-all-r (tagged-element->elem (tree->head y))
                          (tree->right x))
                (tree-in a (tree->right x)))
           (tree-in a (tree->right y)))
  :use tree-in-when-tree-in-and-tree-subset-p
  :disable tree-in-when-tree-in-and-tree-subset-p)

(defrule tree-subset-p-of-tree->right-tree->right-when-tree-subset-p-and-<<-all-r
  (implies (and (tree-subset-p x y)
                (bstp y)
                (<<-all-r (tagged-element->elem (tree->head y))
                          (tree->right x)))
           (tree-subset-p (tree->right x) (tree->right y)))
  :use (:instance tree-subset-p-becomes-tree-subset-p-sk
                  (x (tree->right x))
                  (y (tree->right y)))
  :enable tree-subset-p-sk)

(defrule tree-subset-p-of-tree->right-tree->right-when-tree-subset-p-and-equal-tree->head-tree->head
  (implies (and (tree-subset-p x y)
                (bstp x)
                (bstp y)
                (equal (tagged-element->elem (tree->head x))
                       (tagged-element->elem (tree->head y))))
           (tree-subset-p (tree->right x) (tree->right y)))
  :disable tree-subset-p-of-tree->right-tree->right-when-tree-subset-p-and-<<-all-r
  :use tree-subset-p-of-tree->right-tree->right-when-tree-subset-p-and-<<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I think this is getting in a cycle of rewriting
;;   (equal (tagged-element->elem x) (tagged-element->elem y))
;; to
;;   (equal x y)
;; and back again.
;; Actually, I'm not sure that is what is happening. IDK wtf is happening.
(defrule tree-subset-p-antisymmetry-weak
  (implies (and (treep x)
                (treep y)
                (bstp x)
                (bstp y)
                (heapp x)
                (heapp y)
                (tree-subset-p x y)
                (tree-subset-p y x))
           (equal x y))
  :rule-classes nil
  :induct (tree-bi-induct x y)
  :hints ('(:use equal-when-treep))
  ;; For some reason, I can't just enable this (enters a loop).
  ;; :enable equal-when-treep
  )

;;;;;;;;;;;;;;;;;;;;

(defruled tree-subset-p-antisymmetry
  (implies (and (treep x)
                (treep y)
                (bstp x)
                (bstp y)
                (heapp x)
                (heapp y))
           (equal (and (tree-subset-p x y)
                       (tree-subset-p y x))
                  (equal x y)))
  :use tree-subset-p-antisymmetry-weak)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-double-containment-no-backchain-limit
  (implies (and (treep x)
                (treep y)
                (bstp x)
                (bstp y)
                (heapp x)
                (heapp y))
           (equal (equal x y)
                  (and (tree-subset-p x y)
                       (tree-subset-p y x))))
  :by tree-subset-p-antisymmetry)

(defruled tree-double-containment
  (implies (and (treep x)
                (treep y)
                (bstp x)
                (bstp y)
                (heapp x)
                (heapp y))
           (equal (equal x y)
                  (and (tree-subset-p x y)
                       (tree-subset-p y x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :by tree-double-containment-no-backchain-limit)
