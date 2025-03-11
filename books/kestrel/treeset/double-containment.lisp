; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/defrule" :dir :system)

(include-book "in-defs")
(include-book "set-defs")
(include-book "subset-defs")
(include-book "total-order")

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
(local (include-book "set"))
(local (include-book "subset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable <<-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: refactor to a less manual proof
(defrulel head-when-subset-subset
  (implies (and (subset x y)
                ;; TODO: use loop-stoppers instead of syntaxp?
                (syntaxp (<< y x))
                (subset y x))
           (equal (head x)
                  (head y)))
  :disable (heap<-of-head-and-arg2-when-in-of-arg2
            in-when-in-and-subset
            ;; TODO: why does this rule sabotage the proof?
            subset-when-not-in-of-head-cheap)
  :use ((:instance heap<-of-head-and-arg2-when-in-of-arg2
                   (x (head x))
                   (set y))
        (:instance heap<-of-head-and-arg2-when-in-of-arg2
                   (x (head y))
                   (set x))
        (:instance in-when-in-and-subset
                   (a (head x))
                   (x y)
                   (y x))
        (:instance in-when-in-and-subset
                   (a (head y))
                   (x x)
                   (y y)))
  :cases ((emptyp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Clean up this pair

(defruledl equal-when-binary-tree-p
  (implies (and (binary-tree-p x)
                (binary-tree-p y))
           (equal (equal x y)
                  (if (tree-emptyp x)
                      (tree-emptyp y)
                    (and (not (tree-emptyp y))
                         (equal (tree-head x)
                                (tree-head y))
                         (equal (tree-left x)
                                (tree-left y))
                         (equal (tree-right x)
                                (tree-right y))))))
  :enable (binary-tree-p
           tree-emptyp
           tree-head
           tree-left
           tree-right))

(defruledl equal-when-setp
  (implies (and (syntaxp (atom x))
                (setp x)
                (setp y)
                (syntaxp (atom y)))
           (equal (equal x y)
                  (if (emptyp x)
                      (emptyp y)
                    (and (not (emptyp y))
                         (equal (head x)
                                (head y))
                         (equal (left x)
                                (left y))
                         (equal (right x)
                                (right y))))))
  :enable (setp
           emptyp
           head
           left
           right
           binary-tree-p
           tree-emptyp
           tree-head
           tree-left
           tree-right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-tree-left-when-tree-in-and-bst<-all
  (implies (and (bst<-all-r (tree-head y) (tree-right y))
                (bst<-all-l (tree-left x) (tree-head y))
                (tree-in a (tree-left x))
                (tree-in a y))
           (tree-in a (tree-left y)))
  :enable (tree-in
           bst<-rules)
  :disable bst<-when-bst<-all-l-and-tree-in-forward-chaining
  :use ((:instance bst<-when-bst<-all-l-and-tree-in
                   (x a)
                   (y (tree-head y))
                   (tree (tree-left x)))))

;; MOVE / better rule
;; (defrule bst<-all-r-of-tree-head-and-tree-right-when-setp
;;   (implies (setp set)
;;            (bst<-all-r (tree-head set)
;;                        (tree-right set))))

(defrule in-of-left-when-in-of-left-of-subset-and-bst<-all-l
  (implies (and (subset x y)
                (bst<-all-l (left x) (head y))
                (in a (left x)))
           (in a (left y)))
  :enable (in
           head
           left)
  :disable in-when-in-and-subset
  :use ((:instance in-when-in-and-subset
                   (a a)
                   (x y)
                   (y x))))

(defrule subset-of-left-left-when-subset-and-bst<-all-l
  (implies (and (subset x y)
                (bst<-all-l (left x) (head y)))
           (subset (left x) (left y)))
  :enable (pick-a-point
           subset))

(defrule subset-of-left-left-when-subset-and-equal-head-head
  (implies (and (subset x y)
                (equal (head x) (head y)))
           (subset (left x) (left y)))
  :enable (head
           left
           sfix)
  :disable subset-of-left-left-when-subset-and-bst<-all-l
  :use subset-of-left-left-when-subset-and-bst<-all-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-tree-right-when-tree-in-and-bst<-all
  (implies (and (bst<-all-l (tree-left y) (tree-head y))
                (bst<-all-r (tree-head y) (tree-right x))
                (tree-in a (tree-right x))
                (tree-in a y))
           (tree-in a (tree-right y)))
  :enable (tree-in
           bst<-rules)
  :disable bst<-when-bst<-all-r-and-tree-in-forward-chaining
  :use ((:instance bst<-when-bst<-all-r-and-tree-in
                   (x (tree-head y))
                   (y a)
                   (tree (tree-right x)))))

;; MOVE / better rule
;; (defrule bst<-all-l-of-tree-left-and-tree-head-when-setp
;;   (implies (setp set)
;;            (bst<-all-l (tree-left set)
;;                      (tree-head set))))

(defrule in-of-right-when-in-of-right-of-subset-and-bst<-all-r
  (implies (and (subset x y)
                (bst<-all-r (head y) (right x))
                (in a (right x)))
           (in a (right y)))
  :enable (in
           head
           right)
  :disable in-when-in-and-subset
  :use ((:instance in-when-in-and-subset
                   (x y)
                   (y x))))

(defrule subset-of-right-right-when-subset-and-bst<-all-r
  (implies (and (subset x y)
                (bst<-all-r (head y) (right x)))
           (subset (right x) (right y)))
  :enable (pick-a-point
           subset))

(defrule subset-of-right-right-when-subset-and-equal-head-head
  (implies (and (subset x y)
                (equal (head x) (head y)))
           (subset (right x) (right y)))
  :enable (head
           right
           sfix)
  :disable subset-of-right-right-when-subset-and-bst<-all-r
  :use subset-of-right-right-when-subset-and-bst<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule subset-antisymmetry-weak
  (implies (and (setp x)
                (setp y)
                (subset x y)
                (subset y x))
           (equal x y))
  :rule-classes nil
  :induct (set-bi-induct x y)
  :enable equal-when-setp)

;;;;;;;;;;;;;;;;;;;;

(defruled subset-antisymmetry
  (implies (and (setp x)
                (setp y))
           (equal (and (subset x y)
                       (subset y x))
                  (equal x y)))
  :use subset-antisymmetry-weak)

;;;;;;;;;;;;;;;;;;;;

(defsection double-containment
  :parents (set)
  :short "Prove set equalities via subset antisymmetry."
  :long
  (xdoc::topstring
    (xdoc::p
      "This mirrors the @(see set::std/osets) rule, @(see
       set::double-containment). Here, we disable it by default.")
    (xdoc::p
      "The proof of antisymmetry is nontrivial. The intuition is that for an
       arbitrary nonempty set, the root of the tree is necessarily the maximum
       element with respect to @(tsee heap<). Then which of the remaining elements
       are in the left and right subtrees is determined by the binary search
       tree property. This reasoning requires and induction over the tree
       structure of both sets simultaneously."))

  (defruled equal-becomes-subset-when-setp
    (implies (and (setp x)
                  (setp y))
             (equal (equal x y)
                    (and (subset x y)
                         (subset y x))))
    :use subset-antisymmetry)

  (defruled double-containment
    (implies (and (setp x)
                  (setp y))
             (equal (equal x y)
                    (and (subset x y)
                         (subset y x))))
    :use subset-antisymmetry
    :rule-classes ((:rewrite :backchain-limit-lst (1 1)))))
