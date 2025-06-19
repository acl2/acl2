; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "binary-tree-defs")
(include-book "in-defs")
(include-book "rotate-defs")
(include-book "set-defs")
(include-book "subset-defs")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "binary-tree"))
(local (include-book "bst"))
(local (include-book "bst-order"))
(local (include-book "heap"))
(local (include-book "heap-order"))
(local (include-book "in"))
(local (include-book "pick-a-point"))
(local (include-book "rotate"))
(local (include-book "set"))
(local (include-book "subset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-split
  (x
   (tree binary-tree-p))
  :returns (mv (in booleanp :rule-classes :type-prescription)
               (left binary-tree-p)
               (right binary-tree-p))
  :parents (implementation)
  :short "Split a tree into two disjoint subtrees."
  :long
  (xdoc::topstring
   (xdoc::p
     "When @('tree') is a @('set'), @('(tree-split x tree)') yields
      @('(mv in left right)') where:")
   (xdoc::ul
     (xdoc::li "@('in') is a boolean representing @('(tree-in x tree)').")
     (xdoc::li "@('left') is a @('set') containing all elements of @('tree')
                less than @('x') (with respect to @('bst<')).")
     (xdoc::li "@('right') is a @('set') containing all elements of @('tree')
                greater than @('x') (with respect to @('bst<'))."))
   (xdoc::p
     "The implementation is comparable to @('tree-insert') if we were to
      pretend @('x') is maximal with respect to @('heap<')."))
  (b* (((when (tree-emptyp tree))
        (mv nil nil nil))
       ((when (equal x (tree-head tree)))
        (mv t (tree-left tree) (tree-right tree))))
    (if (bst< x (tree-head tree))
        (b* (;; Interpret as a tree-node (use x instead of in)
             ;; (may violate heapp)
             ((mv in left$ right$)
              (tree-split x (tree-left tree))))
          (mbe :logic (let ((tree$ (rotate-right
                                     (tree-node (tree-head tree)
                                                (tree-node x left$ right$)
                                                (tree-right tree)))))
                        (mv in (tree-left tree$) (tree-right tree$)))
               ;; TODO: not clear this isn't simpler than the :logic branch
               ;; Also not clear whether the compiler couldn't just make this
               ;;   simplification (since rotate is inlined).
               :exec (mv in
                         left$
                         (tree-node (tree-head tree)
                                    right$
                                    (tree-right tree)))))
      (b* (((mv in left$ right$)
            (tree-split x (tree-right tree))))
        (mbe :logic (let ((tree$ (rotate-left
                                   (tree-node (tree-head tree)
                                              (tree-left tree)
                                              (tree-node x left$ right$)))))
                      (mv in (tree-left tree$) (tree-right tree$)))
             :exec (mv in
                       (tree-node (tree-head tree)
                                  (tree-left tree)
                                  left$)
                       right$)))))
  :hints (("Goal" :in-theory (enable o-p o< o-finp)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-split-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (tree-split a x)
                  (tree-split a y)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((tree-split a x)
           (tree-split a y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-split.left-when-type-prescription
  (or (consp (mv-nth 1 (tree-split x tree)))
      (equal (mv-nth 1 (tree-split x tree)) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-split)

(defrule tree-split.right-when-type-prescription
  (or (consp (mv-nth 2 (tree-split x tree)))
      (equal (mv-nth 2 (tree-split x tree)) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled tree-split.in-when-tree-emptyp
  (implies (tree-emptyp tree)
           (not (mv-nth 0 (tree-split x tree))))
  :enable tree-split)

(defrule tree-split.in-when-tree-emptyp-cheap
  (implies (tree-emptyp tree)
           (not (mv-nth 0 (tree-split x tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-split.in-when-tree-emptyp)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-emptyp-of-tree-split.left-when-tree-emptyp
  (implies (tree-emptyp tree)
           (tree-emptyp (mv-nth 1 (tree-split x tree))))
  :enable tree-split)

(defrule tree-emptyp-of-tree-split.left-when-tree-emptyp-cheap
  (implies (tree-emptyp tree)
           (tree-emptyp (mv-nth 1 (tree-split x tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-emptyp-of-tree-split.left-when-tree-emptyp)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-emptyp-of-tree-split.right-when-tree-emptyp
  (implies (tree-emptyp tree)
           (tree-emptyp (mv-nth 2 (tree-split x tree))))
  :enable tree-split)

(defrule tree-emptyp-of-tree-split.right-when-tree-emptyp-cheap
  (implies (tree-emptyp tree)
           (tree-emptyp (mv-nth 2 (tree-split x tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-emptyp-of-tree-split.right-when-tree-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-split.in-when-bst-p
  (implies (bst-p tree)
           (equal (mv-nth 0 (tree-split x tree))
                  (tree-in x tree)))
  :induct t
  :enable (tree-split
           tree-in
           bst-p
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-of-tree-split.left-when-bst<-all-l
  (implies (bst<-all-l tree y)
           (bst<-all-l (mv-nth 1 (tree-split x tree)) y))
  :induct t
  :enable tree-split)

(defrule bst<-all-l-of-tree-split.left-when-bst<-all-l-cheap
  (implies (bst<-all-l tree y)
           (bst<-all-l (mv-nth 1 (tree-split x tree)) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst<-all-l-of-tree-split.left-when-bst<-all-l)

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-of-tree-split.right-when-bst<-all-l
  (implies (bst<-all-l tree y)
           (bst<-all-l (mv-nth 2 (tree-split x tree)) y))
  :induct t
  :enable tree-split)

(defrule bst<-all-l-of-tree-split.right-when-bst<-all-l-cheap
  (implies (bst<-all-l tree y)
           (bst<-all-l (mv-nth 2 (tree-split x tree)) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst<-all-l-of-tree-split.right-when-bst<-all-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-r-of-arg1-and-tree-split.left-when-bst<-all-r
  (implies (bst<-all-r x tree)
           (bst<-all-r x (mv-nth 1 (tree-split y tree))))
  :induct t
  :enable tree-split)

(defrule bst<-all-r-of-arg1-and-tree-split.left-when-bst<-all-r-cheap
  (implies (bst<-all-r x tree)
           (bst<-all-r x (mv-nth 1 (tree-split y tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst<-all-r-of-arg1-and-tree-split.left-when-bst<-all-r)

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-r-of-arg1-and-tree-split.right-when-bst<-all-r
  (implies (bst<-all-r x tree)
           (bst<-all-r x (mv-nth 2 (tree-split y tree))))
  :induct t
  :enable tree-split)

(defrule bst<-all-r-of-arg1-and-tree-split.right-when-bst<-all-r-cheap
  (implies (bst<-all-r x tree)
           (bst<-all-r x (mv-nth 2 (tree-split y tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst<-all-r-of-arg1-and-tree-split.right-when-bst<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-when-bst<-all-l-of-tree-split.left-and-tree-split.right
  (implies (and (bst<-all-l (mv-nth 1 (tree-split x tree)) y)
                (bst<-all-l (mv-nth 2 (tree-split x tree)) y)
                (bst< x y))
           (bst<-all-l tree y))
  :induct t
  :enable tree-split)

(defruled bst<-all-r-when-bst<-all-l-of-arg1-and-tree-split.left-and-tree-split.right
  (implies (and (bst<-all-r x (mv-nth 1 (tree-split y tree)))
                (bst<-all-r x (mv-nth 2 (tree-split y tree)))
                (bst< x y))
           (bst<-all-r x tree))
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst-p-of-tree-split.left-when-bst-p
  (implies (bst-p tree)
           (bst-p (mv-nth 1 (tree-split x tree))))
  :induct t
  :enable (tree-split
           bst-p))

(defrule bst-p-of-tree-split.right-when-bst-p
  (implies (bst-p tree)
           (bst-p (mv-nth 2 (tree-split x tree))))
  :induct t
  :enable (tree-split
           bst-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-tree-split.left-of-arg1-and-arg1
  (implies (bst-p tree)
           (bst<-all-l (mv-nth 1 (tree-split x tree)) x))
  :induct t
  :enable (tree-split
           bst-p
           bst<-all-extra-rules
           bst<-rules))

(defrule bst<-all-r-of-arg1-and-tree-split.right-of-arg1
  (implies (bst-p tree)
           (bst<-all-r x (mv-nth 2 (tree-split x tree))))
  :induct t
  :enable (tree-split
           bst-p
           bst<-all-extra-rules
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled heap<-all-l-of-tree-split.left-when-heap<-all-l
  (implies (heap<-all-l tree y)
           (heap<-all-l (mv-nth 1 (tree-split x tree)) y))
  :induct t
  :enable tree-split)

(defrule heap<-all-l-of-tree-split.left-when-heap<-all-l-cheap
  (implies (heap<-all-l tree y)
           (heap<-all-l (mv-nth 1 (tree-split x tree)) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable heap<-all-l-of-tree-split.left-when-heap<-all-l)

;;;;;;;;;;;;;;;;;;;;

(defruled heap<-all-l-of-tree-split.right-when-heap<-all-l
  (implies (heap<-all-l tree y)
           (heap<-all-l (mv-nth 2 (tree-split x tree)) y))
  :induct t
  :enable tree-split)

(defrule heap<-all-l-of-tree-split.right-when-heap<-all-l-cheap
  (implies (heap<-all-l tree y)
           (heap<-all-l (mv-nth 2 (tree-split x tree)) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable heap<-all-l-of-tree-split.right-when-heap<-all-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled heap<-all-l-when-heap<-all-l-of-tree-split.left-and-tree-split.right
  (implies (and (heap<-all-l (mv-nth 1 (tree-split x tree)) y)
                (heap<-all-l (mv-nth 2 (tree-split x tree)) y)
                (heap< x y))
           (heap<-all-l tree y))
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-split.left-when-heapp
  (implies (heapp tree)
           (heapp (mv-nth 1 (tree-split x tree))))
  :induct t
  :enable tree-split)

(defrule heapp-of-tree-split.right-when-heapp
  (implies (heapp tree)
           (heapp (mv-nth 2 (tree-split x tree))))
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule setp-of-tree-split.left-when-setp
  (implies (setp tree)
           (setp (mv-nth 1 (tree-split x tree))))
  :enable setp)

(defrule setp-of-tree-split.right-when-setp
  (implies (setp tree)
           (setp (mv-nth 2 (tree-split x tree))))
  :enable setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled tree-in-when-tree-in-of-tree-split.left
  (implies (tree-in x (mv-nth 1 (tree-split y tree)))
           (tree-in x tree))
  :induct t
  :enable tree-split)

(defrule tree-in-when-tree-in-of-tree-split.left-forward-chaining
  (implies (tree-in x (mv-nth 1 (tree-split y tree)))
           (tree-in x tree))
  :rule-classes :forward-chaining
  :enable tree-in-when-tree-in-of-tree-split.left)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-in-when-tree-in-of-tree-split.right
  (implies (tree-in x (mv-nth 2 (tree-split y tree)))
           (tree-in x tree))
  :induct t
  :enable tree-split)

(defrule tree-in-when-tree-in-of-tree-split.right-forward-chaining
  (implies (tree-in x (mv-nth 2 (tree-split y tree)))
           (tree-in x tree))
  :rule-classes :forward-chaining
  :enable tree-in-when-tree-in-of-tree-split.right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled in-when-in-of-tree-split.left
  (implies (and (setp set)
                (in x (mv-nth 1 (tree-split y set))))
           (in x set))
  :enable in)

(defrule in-when-in-of-tree-split.left-forward-chaining
  (implies (and (in x (mv-nth 1 (tree-split y set)))
                (setp set))
           (in x set))
  :rule-classes :forward-chaining
  :enable in-when-in-of-tree-split.left)

;;;;;;;;;;;;;;;;;;;;

(defruled in-when-in-of-tree-split.right
  (implies (and (setp set)
                (in x (mv-nth 2 (tree-split y set))))
           (in x set))
  :enable in)

(defrule in-when-in-of-tree-split.right-forward-chaining
  (implies (and (in x (mv-nth 2 (tree-split y set)))
                (setp set))
           (in x set))
  :rule-classes :forward-chaining
  :enable in-when-in-of-tree-split.right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-tree-split.left
  (implies (bst-p tree)
           (equal (tree-in x (mv-nth 1 (tree-split y tree)))
                  (and (tree-in x tree)
                       (bst< x y))))
  :induct t
  :enable (tree-split
           tree-in-extra-rules
           bst<-rules
           bst<-all-extra-rules))

(defrule tree-in-of-tree-split.right
  (implies (bst-p tree)
           (equal (tree-in x (mv-nth 2 (tree-split y tree)))
                  (and (tree-in x tree)
                       (bst< y x))))
  :induct t
  :enable (tree-split
           tree-in-extra-rules
           bst<-rules
           bst<-all-extra-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree-split.left
  (implies (setp tree)
           (equal (in x (mv-nth 1 (tree-split y tree)))
                  (and (in x tree)
                       (bst< x y))))
  :enable in)

(defrule in-of-tree-split.right
  (implies (setp tree)
           (equal (in x (mv-nth 2 (tree-split y tree)))
                  (and (in x tree)
                       (bst< y x))))
  :enable in)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: useful?
(defruled tree-in-becomes-tree-in-of-tree-split
  (equal (tree-in x tree)
         (or (and (equal x y)
                  (mv-nth 0 (tree-split y tree)))
             (tree-in x (mv-nth 1 (tree-split y tree)))
             (tree-in x (mv-nth 2 (tree-split y tree)))))
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-r-when-tree-emptyp-of-tree-split.left
  (implies (and (bst-p tree)
                (bst< x y)
                (tree-emptyp (mv-nth 1 (tree-split y tree))))
           (bst<-all-r x tree))
  :induct t
  :enable (tree-split
           bst<-rules
           bst<-all-extra-rules))

;; TODO: is this a reasonable rule?
(defrule bst<-all-r-when-tree-emptyp-of-tree-split.left-forward-chaining
  (implies (and (tree-emptyp (mv-nth 1 (tree-split y tree)))
                (bst< x y)
                (bst-p tree))
           (bst<-all-r x tree))
  :rule-classes :forward-chaining
  :use bst<-all-r-when-tree-emptyp-of-tree-split.left)

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-when-tree-emptyp-of-tree-split.right
  (implies (and (bst-p tree)
                (bst< y x)
                (tree-emptyp (mv-nth 2 (tree-split y tree))))
           (bst<-all-l tree x))
  :induct t
  :enable (tree-split
           bst<-all-extra-rules)
  :prep-lemmas
  ((defrule lemma0
     (implies (and (not (bst< y (tree-head tree)))
                   (bst<-all-l (tree-right tree) x)
                   (bst-p tree)
                   (bst< y x))
              (bst<-all-l tree x))
     :enable (bst<-rules
              bst<-all-extra-rules)
     :disable bst<-trichotomy
     :use ((:instance bst<-trichotomy
                      (x (tree-head tree)))))))

;; TODO: is this a reasonable rule?
(defrule bst<-all-l-when-tree-emptyp-of-tree-split.right-forward-chaining
  (implies (and (tree-emptyp (mv-nth 2 (tree-split y tree)))
                (bst< y x)
                (bst-p tree))
           (bst<-all-l tree x))
  :rule-classes :forward-chaining
  :use bst<-all-l-when-tree-emptyp-of-tree-split.right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-emptyp-of-tree-split.left-when-bst<-all-r
  (implies (bst<-all-r x tree)
           (tree-emptyp (mv-nth 1 (tree-split x tree))))
  :induct t
  :enable tree-split)

(defrule tree-emptyp-of-tree-split.right-when-bst<-all-r
  (implies (bst<-all-l tree x)
           (tree-emptyp (mv-nth 2 (tree-split x tree))))
  :induct t
  :enable (tree-split
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule subset-of-tree-split.left
  (implies (setp set)
           (subset (mv-nth 1 (tree-split x set))
                   set))
  :enable (tree-split
           pick-a-point
           subset))

(defrule subset-of-tree-split.right
  (implies (setp set)
           (subset (mv-nth 2 (tree-split x set))
                   set))
  :enable (tree-split
           pick-a-point
           subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule acl2-count-of-tree-split.left-linear
  (implies (binary-tree-p tree)
           (<= (acl2-count (mv-nth 1 (tree-split x tree)))
               (acl2-count tree)))
  :rule-classes :linear
  :induct t
  :enable tree-split)

(defrule acl2-count-of-tree-split.right-linear
  (<= (acl2-count (mv-nth 2 (tree-split x tree)))
      (acl2-count tree))
  :rule-classes :linear
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled tree-nodes-count-becomes-tree-nodes-count-of-tree-split-when-not-tree-in
  (implies (not (tree-in x tree))
           (equal (tree-nodes-count tree)
                  (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
                     (tree-nodes-count (mv-nth 2 (tree-split x tree))))))
  :induct t
  :enable (tree-split
           tree-nodes-count))

(defruled tree-nodes-count-becomes-tree-nodes-count-of-tree-split
  (implies (bst-p tree)
           (equal (tree-nodes-count tree)
                  (if (tree-in x tree)
                      (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
                         (tree-nodes-count (mv-nth 2 (tree-split x tree)))
                         1)
                    (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
                       (tree-nodes-count (mv-nth 2 (tree-split x tree)))))))
  :induct t
  :enable (tree-split
           tree-nodes-count
           bst<-rules))

;; Very awkward rule
;; (defrule tree-nodes-count-becomes-tree-nodes-count-of-tree-split-forward-chaining
;;   (implies (bst-p tree)
;;            (equal (tree-nodes-count tree)
;;                   (if (tree-in x tree)
;;                       (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
;;                          (tree-nodes-count (mv-nth 2 (tree-split x tree)))
;;                          1)
;;                     (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
;;                        (tree-nodes-count (mv-nth 2 (tree-split x tree)))))))
;;   :rule-classes ((:forward-chaining :trigger-terms
;;                   ((tree-nodes-count (mv-nth 1 (tree-split x tree)))
;;                    (tree-nodes-count (mv-nth 2 (tree-split x tree))))))
;;   :use tree-nodes-count-becomes-tree-nodes-count-of-tree-split)

;; Very awkward rule
(defrule tree-nodes-count-becomes-tree-nodes-count-of-tree-split-linear
  (implies (bst-p tree)
           (equal (tree-nodes-count tree)
                  (if (tree-in x tree)
                      (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
                         (tree-nodes-count (mv-nth 2 (tree-split x tree)))
                         1)
                    (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
                       (tree-nodes-count (mv-nth 2 (tree-split x tree)))))))
  :rule-classes ((:linear :trigger-terms
                  ((tree-nodes-count (mv-nth 1 (tree-split x tree)))
                   (tree-nodes-count (mv-nth 2 (tree-split x tree))))))
  :use tree-nodes-count-becomes-tree-nodes-count-of-tree-split)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-nodes-count-of-tree-split.left-and-tree-split.right-linear
  (implies (bst-p tree)
           (<= (tree-nodes-count tree)
               (+ (tree-nodes-count (mv-nth 1 (tree-split x tree)))
                  (tree-nodes-count (mv-nth 2 (tree-split x tree)))
                  1)))
  :rule-classes ((:linear :trigger-terms
                  ((tree-nodes-count (mv-nth 1 (tree-split x tree)))
                   (tree-nodes-count (mv-nth 2 (tree-split x tree))))))
  :use tree-nodes-count-becomes-tree-nodes-count-of-tree-split)

(defruled tree-nodes-count-of-tree-split.left-linear
  (<= (tree-nodes-count (mv-nth 1 (tree-split x tree)))
      (tree-nodes-count tree))
  :rule-classes :linear
  :induct t
  :enable (tree-split
           tree-nodes-count))

(defruled tree-nodes-count-of-tree-split.right-linear
  (<= (tree-nodes-count (mv-nth 2 (tree-split x tree)))
      (tree-nodes-count tree))
  :rule-classes :linear
  :induct t
  :enable (tree-split
           tree-nodes-count))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-split-of-tree-head
  (equal (tree-split (tree-head tree) tree)
         (mv (not (tree-emptyp tree))
             (tree-left tree)
             (tree-right tree)))
  :enable tree-split)

(defrule tree-split-of-bind-tree-head-cheap
  (implies (equal x (tree-head tree))
           (equal (tree-split x tree)
                  (mv (not (tree-emptyp tree))
                      (tree-left tree)
                      (tree-right tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-split-of-tree-head)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy tree-split-extra-rules
  '(tree-split.in-when-tree-emptyp
    tree-emptyp-of-tree-split.left-when-tree-emptyp
    tree-emptyp-of-tree-split.right-when-tree-emptyp
    bst<-all-l-of-tree-split.left-when-bst<-all-l
    bst<-all-l-of-tree-split.right-when-bst<-all-l
    bst<-all-r-of-arg1-and-tree-split.left-when-bst<-all-r
    bst<-all-r-of-arg1-and-tree-split.right-when-bst<-all-r
    bst<-all-l-when-bst<-all-l-of-tree-split.left-and-tree-split.right
    bst<-all-r-when-bst<-all-l-of-arg1-and-tree-split.left-and-tree-split.right
    heap<-all-l-of-tree-split.left-when-heap<-all-l
    heap<-all-l-of-tree-split.right-when-heap<-all-l
    heap<-all-l-when-heap<-all-l-of-tree-split.left-and-tree-split.right
    tree-in-when-tree-in-of-tree-split.left
    tree-in-when-tree-in-of-tree-split.right
    in-when-in-of-tree-split.left
    in-when-in-of-tree-split.right))
