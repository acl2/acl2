; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "cardinality-defs")
(include-book "in-defs")
(include-book "join-defs")
(include-book "set-defs")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "binary-tree"))
(local (include-book "bst"))
(local (include-book "bst-order"))
(local (include-book "cardinality"))
(local (include-book "double-containment"))
(local (include-book "heap"))
(local (include-book "heap-order"))
(local (include-book "in"))
(local (include-book "join"))
(local (include-book "pick-a-point"))
(local (include-book "set"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-delete
  (x
   (tree binary-tree-p))
  (declare (xargs :type-prescription (or (consp (tree-delete x tree))
                                         (equal (tree-delete x tree) nil))))
  :returns (tree$ binary-tree-p)
  :parents (implementation)
  :short "Remove a value from the tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "The tree is expected to be a binary search tree. If it is not, the
      element @('x') intended to be deleted might outside the search path and
      thus remain in the tree.")
   (xdoc::p
     "After deletion, the tree is rebalanced with respect to the @(tsee
     heapp) property."))
  (b* (((when (tree-emptyp tree))
        nil)
       ((when (equal x (tree-head tree)))
        (cond ((tree-emptyp (tree-left tree))
               (tree-right tree))
              ((tree-emptyp (tree-right tree))
               (tree-left tree))
              (t (tree-join-at (tree-head tree)
                               (tree-left tree)
                               (tree-right tree))))))
    (if (bst< x (tree-head tree))
        ;; TODO: instead of using tree-node-with-hint, return a flag indicating
        ;; whether or not the subtree we recursed on changed.
        (tree-node-with-hint (tree-head tree)
                             (tree-delete x (tree-left tree))
                             (tree-right tree)
                             tree)
      (tree-node-with-hint (tree-head tree)
                           (tree-left tree)
                           (tree-delete x (tree-right tree))
                           tree)))
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-delete-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (tree-delete a x)
                  (tree-delete a y)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((tree-delete a x)
           (tree-delete a y)))

(defrulel tree-emptyp-of-tree-delete-when-tree-emptyp
  (implies (tree-emptyp tree)
           (tree-emptyp (tree-delete x tree)))
  :enable tree-delete)

(defrule tree-in-of-tree-delete
  (implies (bst-p tree)
           (equal (tree-in x (tree-delete y tree))
                  (and (not (equal x y))
                       (tree-in x tree))))
  :induct t
  :enable (tree-delete
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-tree-delete
  (implies (bst<-all-l tree y)
           (bst<-all-l (tree-delete x tree) y))
  :induct t
  :enable (bst<-all-l
           tree-delete))

(defrule bst<-all-l-when-not-bst<-all-l-of-tree-delete-forward-chaining
  (implies (not (bst<-all-l (tree-delete y tree) x))
           (not (bst<-all-l tree x)))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-r-of-arg1-and-tree-delete
  (implies (bst<-all-r x tree)
           (bst<-all-r x (tree-delete y tree)))
  :induct t
  :enable (bst<-all-r
           tree-delete))

(defrule bst<-all-r-when-not-bst<-all-r-of-arg1-and-tree-delete-forward-chaining
  (implies (not (bst<-all-r x (tree-delete y tree)))
           (not (bst<-all-r x tree)))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst-p-of-tree-delete-when-bst-p
  (implies (bst-p tree)
           (bst-p (tree-delete x tree)))
  :induct t
  :enable (tree-delete
           bst-p
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-delete
  (implies (heap<-all-l tree x)
           (heap<-all-l (tree-delete y tree) x))
  :induct t
  :enable (heap<-all-l
           tree-delete))

(defrule heap<-all-l-when-not-heap<-all-l-of-tree-delete-forward-chaining
  (implies (not (heap<-all-l (tree-delete y tree) x))
           (not (heap<-all-l tree x)))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-delete
  (implies (and (heapp tree)
                (bst-p tree))
           (heapp (tree-delete x tree)))
  :induct t
  :enable tree-delete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule setp-of-tree-delete-when-setp
  (implies (setp tree)
           (setp (tree-delete x tree)))
  :enable setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-nodes-count-of-tree-delete
  (implies (bst-p tree)
           (equal (tree-nodes-count (tree-delete x tree))
                  (if (tree-in x tree)
                      (- (tree-nodes-count tree) 1)
                    (tree-nodes-count tree))))
  :induct t
  :enable (tree-delete
           tree-nodes-count
           bst-p
           bst<-rules
           fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection delete
  :parents (set)
  :short "Remove a value from the set."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(n))$)."))

  (define delete1
    (x
     (set setp))
    (declare (xargs :type-prescription (or (consp (delete1 x set))
                                           (equal (delete1 x set) nil))))
    :returns (set$ setp)
    (tree-delete x (sfix set))
    :no-function t
    :inline t)

  ;;;;;;;;;;;;;;;;;;;;

  (define delete-macro-loop
    ((list true-listp))
    :guard (and (consp list)
                (consp (rest list)))
    (if (endp (rest (rest list)))
        (list 'delete1
              (first list)
              (second list))
      (list 'delete1
            (first list)
            (delete-macro-loop (rest list))))
    :hints (("Goal" :in-theory (enable o< o-finp acl2-count))))

  (defmacro delete (x y &rest rst)
    (declare (xargs :guard t))
    (delete-macro-loop (list* x y rst)))

  (add-macro-fn delete delete1$inline t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule delete-when-set-equiv-congruence
  (implies (set-equiv x y)
           (equal (delete a x)
                  (delete a y)))
  :rule-classes :congruence
  :enable (set-equiv
           delete))

;; TODO: remove/localize after introduction of more general rule
(defrule emptyp-of-delete-when-emptyp
  (implies (emptyp set)
           (emptyp (delete x set)))
  :enable (emptyp
           delete))

(defrule in-of-delete
  (equal (in x (delete y set))
         (and (not (equal x y))
              (in x set)))
  :enable (in
           delete
           sfix))

(defrule delete-commutative
  (equal (delete y x set)
         (delete x y set))
  :enable (double-containment
           pick-a-point
           subset))

;; TODO
;; (include-book "insert")
;; (defrule emptyp-of-delete
;;   (equal (emptyp (delete x set))
;;          (or (emptyp set)
;;              (equal set (insert x set))))
;;   :enable (double-containment
;;            pick-a-point
;;            subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-delete
  (implies (bst<-all-l set y)
           (bst<-all-l (delete x set) y))
  :enable (delete
           sfix))

(defrule bst<-all-l-when-not-bst<-all-l-of-delete-forward-chaining
  (implies (not (bst<-all-l (delete y set) x))
           (not (bst<-all-l set x)))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-r-of-arg1-and-delete
  (implies (bst<-all-r x set)
           (bst<-all-r x (delete y set)))
  :enable (delete
           sfix))

(defrule bst<-all-r-when-not-bst<-all-r-of-arg1-and-delete-forward-chaining
  (implies (not (bst<-all-r x (delete y set)))
           (not (bst<-all-r x set)))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-delete
  (implies (heap<-all-l set x)
           (heap<-all-l (delete y set) x))
  :enable (delete
           sfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cardinality-of-delete
  (equal (cardinality (delete x set))
         (if (in x set)
             (- (cardinality set) 1)
           (cardinality set)))
  :enable (cardinality
           delete
           in
           sfix))

(defrule cardinality-of-delete-when-in
  (implies (in x set)
           (equal (cardinality (delete x set))
                  (- (cardinality set) 1)))
  :use cardinality-of-delete)

(defrule cardinality-of-delete-when-not-in
  (implies (not (in x set))
           (equal (cardinality (delete x set))
                  (cardinality set)))
  :use cardinality-of-delete)
