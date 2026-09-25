; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "set-defs")
(include-book "cardinality-defs")
(include-book "in-defs")
(include-book "min-max-defs")
(include-book "subset-defs")
(include-book "insert-defs")
(include-book "delete-defs")
(include-book "union-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "set"))
(local (include-book "cardinality"))
(local (include-book "in"))
(local (include-book "min-max"))
(local (include-book "insert"))
(local (include-book "delete"))
(local (include-book "subset"))
(local (include-book "extensionality"))
(local (include-book "union"))
(local (include-book "intersect"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cons-all-r
  (x
   (set setp))
  :returns (set setp)
  :parents (product)
  :short "Cons an element to each element of a @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The elements are regular @('cons')es.
     This is primarily used as a helper for @(tsee product).")
   (xdoc::p
    "Note that the current implementation is inefficient.
     It should be possible to construct the set in @($O(n)$) time,
     exploiting the fact that the pairs may be built in-order."))
  (if (emptyp set)
      (empty)
    (let ((min (min set)))
      (insert (cons x min)
              (cons-all-r x (delete min set)))))
  :verify-guards :after-returns
  :measure (cardinality set))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule cons-all-r-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (cons-all-r x set0)
                  (cons-all-r x set1)))
  :rule-classes :congruence
  :induct t
  :enable cons-all-r)

(defrule emptyp-of-cons-all-r
  (equal (emptyp (cons-all-r x set))
         (emptyp set))
  :expand (cons-all-r x set))

(defrule in-of-cons-all-r
  (equal (in a (cons-all-r x set))
         (and (consp a)
              (equal (car a) x)
              (in (cdr a) set)))
  :induct t
  :enable cons-all-r)

(defrule monotonicity-of-cons-all-r
  (implies (subset set0 set1)
           (subset (cons-all-r x set0)
                   (cons-all-r x set1)))
  :enable pick-a-point)

(defruled cons-all-r-when-emptyp
  (implies (emptyp set)
           (equal (cons-all-r x set)
                  (empty)))
  :enable extensionality)

(defrule cons-all-r-when-emptyp-cheap
  (implies (emptyp set)
           (equal (cons-all-r x set)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by cons-all-r-when-emptyp)

(defrule cons-all-r-of-empty
  (equal (cons-all-r x (empty))
         (empty))
  :enable cons-all-r-when-emptyp)

(defrule cardinality-of-cons-all-r
  (equal (cardinality (cons-all-r x set))
         (cardinality set))
  :induct t
  :enable (cons-all-r
           acl2::fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define product
  ((x setp)
   (y setp))
  :returns (set setp)
  :parents (treeset)
  :short "Create the Cartesian product of two @(see treeset)s."
  :long
  (xdoc::topstring
   (xdoc::p
    "The elements are regular @('cons')es.")
   (xdoc::p
    "Note that the current implementation is inefficient.
     It should be possible to construct the set in @($O(nm)$) time,
     exploiting the fact that the pairs may be built in-order."))
  (if (emptyp x)
      (empty)
    (let ((min (min x)))
      (union (cons-all-r min y)
             (product (delete min x) y))))
  :verify-guards :after-returns
  :measure (cardinality x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule product-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (product x0 y)
                  (product x1 y)))
  :rule-classes :congruence
  :induct t
  :enable product)

(defrule product-when-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (product x y0)
                  (product x y1)))
  :rule-classes :congruence
  :induct t
  :enable product)

(defrule emptyp-of-product
  (equal (emptyp (product x y))
         (or (emptyp x)
             (emptyp y)))
  :induct t
  :enable product)

(defrule in-of-product
  (equal (in a (product x y))
         (and (consp a)
              (in (car a) x)
              (in (cdr a) y)))
  :induct t
  :enable product)

(defrule monotonicity-of-product
  (implies (and (subset x0 x1)
                (subset y0 y1))
           (subset (product x0 y0)
                   (product x1 y1)))
  :enable pick-a-point)

(defruled product-when-emptyp-of-arg1
  (implies (emptyp x)
           (equal (product x y)
                  (empty)))
  :enable extensionality)

(defrule product-when-emptyp-of-arg1-cheap
  (implies (emptyp x)
           (equal (product x y)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by product-when-emptyp-of-arg1)

(defrule product-of-empty
  (equal (product (empty) y)
         (empty))
  :enable product-when-emptyp-of-arg1)

(defruled product-when-emptyp-of-arg2
  (implies (emptyp y)
           (equal (product x y)
                  (empty)))
  :enable extensionality)

(defrule product-when-emptyp-of-arg2-cheap
  (implies (emptyp y)
           (equal (product x y)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by product-when-emptyp-of-arg2)

(defrule product-of-arg1-and-empty
  (equal (product x (empty))
         (empty))
  :enable product-when-emptyp-of-arg2)

(defrulel intersect-of-cons-all-r-and-product-when-not-in
  (implies (not (in a x))
           (equal (intersect (cons-all-r a y0)
                             (product x y1))
                  (empty)))
  :enable extensionality)

(defrule cardinality-of-product
  (equal (cardinality (product x y))
         (* (cardinality x)
            (cardinality y)))
  :induct t
  :enable (product
           acl2::fix))
