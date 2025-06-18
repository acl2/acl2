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
(include-book "rotate-defs")
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
(local (include-book "pick-a-point"))
(local (include-book "rotate"))
(local (include-book "set"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-insert
  (x
   (tree binary-tree-p))
  :returns (tree$ binary-tree-p)
  :parents (implementation)
  :short "Insert a value into the tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "The element is inserted with respect to the binary search tree ordering
      and then rebalanced with respect to the @(tsee heapp) property."))
  (b* (((when (tree-emptyp tree))
        (tree-node x nil nil))
       ((when (equal x (tree-head tree)))
        (tree-fix tree))
       (lt (bst< x (tree-head tree))))
    (if lt
        (b* ((left$ (tree-insert x (tree-left tree)))
             (tree$ (tree-node-with-hint (tree-head tree)
                                         left$
                                         (tree-right tree)
                                         tree)))
          (if (heap< (tree-head tree)
                  (tree-head left$))
              (rotate-right tree$)
            tree$))
      (b* ((right$ (tree-insert x (tree-right tree)))
           (tree$ (tree-node-with-hint (tree-head tree)
                                       (tree-left tree)
                                       right$
                                       tree)))
        (if (heap< (tree-head tree)
                (tree-head right$))
            (rotate-left tree$)
          tree$))))
  :hints (("Goal" :in-theory (enable o< o-finp)))

  ;; Verified below
  :verify-guards nil
  ///

  (defrule tree-emptyp-of-tree-insert
    (not (tree-emptyp (tree-insert x tree)))
    :induct t
    :enable tree-insert)

  (verify-guards tree-insert))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-insert-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (tree-insert a x)
                  (tree-insert a y)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((tree-insert a x)
           (tree-insert a y)))

(defrule tree-insert-type-prescription
  (consp (tree-insert x tree))
  :rule-classes :type-prescription
  :enable tree-emptyp
  :disable tree-emptyp-of-tree-insert
  :use tree-emptyp-of-tree-insert)

(defrule tree-in-of-tree-insert
  (equal (tree-in x (tree-insert y tree))
         (or (equal x y)
             (tree-in x tree)))
  :induct t
  :enable tree-insert)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-tree-insert
  (equal (bst<-all-l (tree-insert y tree) x)
         (and (bst< y x)
              (bst<-all-l tree x)))
  :induct t
  :enable (bst<-all-l
           tree-insert))

(defrule bst<-all-r-of-tree-insert
  (equal (bst<-all-r x (tree-insert y tree))
         (and (bst< x y)
              (bst<-all-r x tree)))
  :induct t
  :enable (bst<-all-r
           tree-insert))

(defrule bst-p-of-tree-insert-when-bst-p
  (implies (bst-p tree)
           (bst-p (tree-insert x tree)))
  :induct t
  :enable (tree-insert
           bst-p
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-insert
  (equal (heap<-all-l (tree-insert y tree) x)
         (and (heap< y x)
              (heap<-all-l tree x)))
  :induct t
  :enable (heap<-all-l
           tree-insert))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl tree-insert-hmax-heap-invariants
  (implies (and (heapp tree)
                ;; In subsequent proofs, `a` will be the head of the parent node
                (heap<-all-l tree a))
           (if (or (tree-emptyp tree)
                   (heap< (tree-head tree) x))
               (and (equal (tree-head (tree-insert x tree))
                           x)
                    (heap<-all-l (tree-left (tree-insert x tree))
                                 a)
                    (heap<-all-l (tree-right (tree-insert x tree))
                                 a))
             (heap<-all-l (tree-insert x tree) a)))
  :induct t
  :enable (tree-insert
           heapp
           heap<-all-l-extra-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: break off some of these lemmas into standalone rules?
(encapsulate ()
  (defrulel lemma0
    (implies (and (not (equal x (tree-head tree)))
                  (not (heap< (tree-head tree)
                              (tree-head (tree-insert x (tree-right tree)))))
                  (heapp tree))
             (heap< x (tree-head tree)))
    :enable heap<-rules
    :use ((:instance tree-insert-hmax-heap-invariants
                     (a (tree-head tree))
                     (tree (tree-right tree)))))

  (defrulel lemma1
    (implies (and (not (equal x (tree-head tree)))
                  (not (heap< (tree-head tree)
                              (tree-head (tree-insert x (tree-left tree)))))
                  (heapp tree))
             (heap< x (tree-head tree)))
    :enable heap<-rules
    :use ((:instance tree-insert-hmax-heap-invariants
                     (a (tree-head tree))
                     (tree (tree-left tree)))))

  (defrulel lemma2
    (implies (heapp tree)
             (heap<-all-l (tree-left (tree-insert x (tree-right tree)))
                          (tree-head tree)))
    :enable heap<-all-l-extra-rules
    :use ((:instance tree-insert-hmax-heap-invariants
                     (a (tree-head tree))
                     (tree (tree-right tree)))))

  (defrulel lemma3
    (implies (and (not (equal x (tree-head tree)))
                  (heapp tree))
             (heap<-all-l (tree-right (tree-insert x (tree-left tree)))
                          (tree-head tree)))
    :enable heap<-all-l-extra-rules
    :use ((:instance tree-insert-hmax-heap-invariants
                     (a (tree-head tree))
                     (tree (tree-left tree)))))

  (defrule heapp-of-tree-insert-when-heapp
    (implies (heapp tree)
             (heapp (tree-insert x tree)))
    :induct t
    :enable tree-insert))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule setp-of-tree-insert-when-setp
  (implies (setp set)
           (setp (tree-insert x set)))
  :enable setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-nodes-count-of-tree-insert
  (implies (bst-p tree)
           (equal (tree-nodes-count (tree-insert x tree))
                  (if (tree-in x tree)
                      (tree-nodes-count tree)
                    (+ 1 (tree-nodes-count tree)))))
  :induct t
  :enable (tree-insert
           tree-nodes-count
           bst-p
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection insert
  :parents (set)
  :short "Add a value (or multiples values) to the set."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(n))$)."))

  (define insert1
    (x
     (set setp))
    :returns (set$ setp)
    (tree-insert x (sfix set))
    :inline t)

  ;;;;;;;;;;;;;;;;;;;;

  (define insert-macro-loop
    ((list true-listp))
    :guard (and (consp list)
                (consp (rest list)))
    (if (endp (rest (rest list)))
        (list 'insert1
              (first list)
              (second list))
      (list 'insert1
            (first list)
            (insert-macro-loop (rest list))))
    :hints (("Goal" :in-theory (enable o< o-finp acl2-count))))

  (defmacro insert (x y &rest rst)
    (declare (xargs :guard t))
    (insert-macro-loop (list* x y rst)))

  (add-macro-fn insert insert1$inline t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule insert-when-set-equiv-congruence
  (implies (set-equiv x y)
           (equal (insert a x)
                  (insert a y)))
  :rule-classes :congruence
  :enable (set-equiv
           insert))

(defrule emptyp-of-insert
  (not (emptyp (insert x set)))
  :enable (emptyp
           insert))

(defrule insert-type-prescription
  (consp (insert x set))
  :rule-classes :type-prescription
  :disable emptyp-of-insert
  :use emptyp-of-insert)

(defrule in-of-insert
  (equal (in x (insert y set))
         (or (equal x y)
             (in x set)))
  :enable (in
           insert))

(defrule insert-commutative
  (equal (insert y x set)
         (insert x y set))
  :enable (double-containment
           pick-a-point
           subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-insert
  (equal (bst<-all-l (insert y set) x)
         (and (bst< y x)
              (bst<-all-l (sfix set) x)))
  :enable insert)

(defrule bst<-all-r-of-insert
  (equal (bst<-all-r x (insert y set))
         (and (bst< x y)
              (bst<-all-r x (sfix set))))
  :enable insert)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-insert
  (equal (heap<-all-l (insert y set) x)
         (and (heap< y x)
              (heap<-all-l (sfix set) x)))
  :enable insert)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cardinality-of-insert
  (equal (cardinality (insert x set))
         (if (in x set)
             (cardinality set)
           (+ 1 (cardinality set))))
  :enable (cardinality
           insert
           in
           sfix))

(defrule cardinality-of-insert-when-in
  (implies (in x set)
           (equal (cardinality (insert x set))
                  (cardinality set)))
  :enable cardinality-of-insert)

(defrule cardinality-of-insert-when-not-in
  (implies (not (in x set))
           (equal (cardinality (insert x set))
                  (+ 1 (cardinality set))))
  :enable cardinality-of-insert)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert-all
  ((list true-listp)
   (set setp))
  :returns (set$ setp)
  :parents (insert)
  :short "Add a list of values to the set."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n\\log(n+m))$), where @($n$) is the size of the list,
      and @($m$) is the size of the set."))
  (if (endp list)
      (sfix set)
    (insert-all (rest list)
                (insert (first list) set))))

(defrule insert-all-type-prescription
  (or (consp (insert-all list set))
      (equal (insert-all list set) nil))
  :rule-classes :type-prescription
  :induct t
  :enable (insert-all
           sfix))

(defrule insert-all-when-consp-of-arg1-type-prescription
  (implies (consp list)
           (consp (insert-all list set)))
  :rule-classes :type-prescription
  :induct t
  :enable insert-all)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule insert-all-when-set-equiv-congruence
  (implies (set-equiv x y)
           (equal (insert-all list x)
                  (insert-all list y)))
  :rule-classes :congruence
  :induct t
  :enable (set-equiv
           insert-all
           ;; TODO: insert shouldn't need to be enabled
           insert))

(defrule emptyp-of-insert-all
  (equal (emptyp (insert-all list set))
         (and (not (consp list))
              (emptyp set)))
  :induct t
  :enable insert-all)

(defrule in-of-insert-all
  (equal (in x (insert-all list set))
         (or (and (member-equal x list) t)
             (in x set)))
  :induct t
  :enable (insert-all
           member-equal)
  :prep-lemmas
  ((defrule in-of-insert-all-when-in
     (implies (in x set)
              (in x (insert-all list set)))
     :induct t
     :enable insert-all)))

;; TODO
;; (defrule insert-all-when-acl2-set-equiv
;;   (implies (acl2::set-equiv x y)
;;            (equal (insert-all x set)
;;                   (insert-all y set)))
;;   :enable (double-containment
;;            pick-a-point
;;            subset))

;; TODO: cardinality

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-list
  ((list true-listp))
  :returns (set$ setp)
  :parents (set)
  :short "Create a set from a list of values."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is just a wrapper around @(tsee insert-all).")
   (xdoc::p
     "Time complexity: @($O(n\\log(n))$)."))
  (insert-all list nil)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-from-list
  (equal (emptyp (from-list list))
         (not (consp list)))
  :enable from-list)

(defrule in-of-from-list
  (equal (in x (from-list list))
         (and (member-equal x list) t))
  :enable from-list)

;; TODO
;; (defrule from-list-when-acl2-set-equiv
;;   (implies (acl2::set-equiv x y)
;;            (equal (insert-all x)
;;                   (insert-all y)))
;;   :enable from-list)

;; TODO: cardinality
