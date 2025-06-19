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

(include-book "std/basic/two-nats-measure" :dir :system)

(include-book "set-defs")
(include-book "sum-acl2-count-defs")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "kestrel/lists-light/len" :dir :system))

(local (include-book "binary-tree"))
(local (include-book "set"))
(local (include-book "sum-acl2-count"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A tail-recursive version of tree-nodes-count
;; TODO: consider using loop$
(define fast-tree-nodes-count
  ((trees binary-tree-listp)
   (acc natp))
  (declare (xargs :type-prescription (natp (fast-tree-nodes-count trees acc))))
  (b* ((acc (mbe :logic (nfix acc)
                 :exec (the unsigned-byte acc))))
    (cond ((endp trees)
           acc)
          ((tree-emptyp (first trees))
           (fast-tree-nodes-count (rest trees) acc))
          (t (fast-tree-nodes-count (list* (tree-left (first trees))
                                           (tree-right (first trees))
                                           (rest trees))
                                    (+ 1 acc)))))
  :measure (acl2::nat-list-measure
            (list (sum-acl2-count trees)
                  (len trees)))
  :hints (("Goal" :in-theory (enable o-p
                                     o<
                                     o-finp
                                     sum-acl2-count
                                     nfix)))
  :guard-hints (("Goal" :in-theory (enable nfix))))

(defrulel fast-tree-nodes-count-when-not-natp-of-arg2
  (implies (not (natp acc))
           (equal (fast-tree-nodes-count trees acc)
                  (fast-tree-nodes-count trees 0)))
  :induct t
  :enable (fast-tree-nodes-count
           nfix))

(defruledl fast-tree-nodes-count-of-arg1-and-+
  (implies (and (natp acc0)
                (natp acc1))
           (equal (fast-tree-nodes-count trees (+ acc0 acc1))
                  (+ (fast-tree-nodes-count trees acc0)
                     acc1)))
  :induct t
  :enable (fast-tree-nodes-count
           nfix))

(defrulel fast-tree-nodes-count-when-syntaxp-not-equal-arg2-0
  (implies (syntaxp (not (equal acc ''0)))
           (equal (fast-tree-nodes-count trees acc)
                  (+ (fast-tree-nodes-count trees 0)
                     (nfix acc))))
  :enable (nfix
           fix)
  :use ((:instance fast-tree-nodes-count-of-arg1-and-+
                   (acc0 0)
                   (acc1 acc))))

(defrulel fast-tree-nodes-count-of-append
  (equal (fast-tree-nodes-count (append trees0 trees1) acc)
         (+ (fast-tree-nodes-count trees0 0)
            (fast-tree-nodes-count trees1 0)
            (nfix acc)))
  :induct t
  :enable (fast-tree-nodes-count
           fix
           append))

(defruledl fast-tree-nodes-count-of-cons
  (equal (fast-tree-nodes-count (cons tree trees) acc)
         (+ (fast-tree-nodes-count (list tree) 0)
            (fast-tree-nodes-count trees 0)
            (nfix acc)))
  :enable (append)
  :disable fast-tree-nodes-count-of-append
  :use ((:instance fast-tree-nodes-count-of-append
                   (trees0 (list tree))
                   (trees1 trees))))

(defrulel fast-tree-nodes-count-of-cons-when-not-singleton
  (implies (syntaxp (not (equal trees ''nil)))
           (equal (fast-tree-nodes-count (cons tree trees) acc)
                  (+ (fast-tree-nodes-count (list tree) 0)
                     (fast-tree-nodes-count trees 0)
                     (nfix acc))))
  :use fast-tree-nodes-count-of-cons)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-nodes-count
  ((tree binary-tree-p))
  (declare (xargs :type-prescription (natp (tree-nodes-count tree))))
  :parents (implementation)
  :short "The number of elements in a tree."
  (mbe :logic (if (tree-emptyp tree)
                  0
                (+ 1
                   (tree-nodes-count (tree-left tree))
                   (tree-nodes-count (tree-right tree))))
       :exec (fast-tree-nodes-count (list tree) 0))
  :inline t
  :hints (("Goal" :in-theory (enable o< o-finp)))
  ;; Verified below
  :verify-guards nil)

(defruled fast-tree-nodes-count-becomes-tree-nodes-count
  (equal (fast-tree-nodes-count (list tree) acc)
         (+ (tree-nodes-count tree)
            (nfix acc)))
  :induct t
  :enable tree-nodes-count
  :expand ((fast-tree-nodes-count (list tree) 0)))

(verify-guards tree-nodes-count$inline
  :hints (("Goal" :in-theory (enable
                               fast-tree-nodes-count-becomes-tree-nodes-count
                               tree-nodes-count
                               fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-nodes-count-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (tree-nodes-count x)
                  (tree-nodes-count y)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((tree-nodes-count x)
           (tree-nodes-count y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled equal-of-tree-nodes-count-and-0-becomes-tree-emptyp
  (equal (equal (tree-nodes-count tree)
                0)
         (tree-emptyp tree))
  :induct t
  :enable (tree-nodes-count
           tree-emptyp
           fix))

(defrule tree-nodes-count-when-tree-emptyp-forward-chaining
  (implies (tree-emptyp tree)
           (equal (tree-nodes-count tree)
                  0))
  :rule-classes :forward-chaining
  :enable equal-of-tree-nodes-count-and-0-becomes-tree-emptyp)

(defrule tree-emptyp-when-equal-tree-nodes-count-and-0-forward-chaining
  (implies (equal (tree-nodes-count tree)
                  0)
           (tree-emptyp tree))
  :rule-classes :forward-chaining
  :enable equal-of-tree-nodes-count-and-0-becomes-tree-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cardinality
  ((set setp))
  (declare (xargs :type-prescription (natp (cardinality set))))
  :parents (set)
  :short "The number of elements in a @(see set)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n)$)."))
  (tree-nodes-count (sfix set))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule cardinality-when-set-equiv-congruence
  (implies (set-equiv x y)
           (equal (cardinality x)
                  (cardinality y)))
  :rule-classes :congruence
  :enable (set-equiv
           cardinality))

(defruled equal-of-cardinality-and-0-becomes-emptyp
  (equal (equal (cardinality set)
                0)
         (emptyp set))
  :enable (cardinality
           emptyp))

(defrule cardinality-when-emptyp-forward-chaining
  (implies (emptyp set)
           (equal (cardinality set)
                  0))
  :rule-classes :forward-chaining
  :enable equal-of-cardinality-and-0-becomes-emptyp)

(defrule emptyp-when-equal-cardinality-and-0-forward-chaining
  (implies (equal (cardinality set)
                  0)
           (emptyp set))
  :rule-classes :forward-chaining
  :enable equal-of-cardinality-and-0-becomes-emptyp)
