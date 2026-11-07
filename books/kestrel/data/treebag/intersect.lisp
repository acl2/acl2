; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEBAG")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "internal/intersect-defs")
(include-book "bag-defs")
(include-book "count-defs")
(include-book "cardinality-defs")
(include-book "subbag-defs")
(include-book "insert-defs")
(include-book "delete-defs")
(include-book "union-defs")
(include-book "sum-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/arithmetic-light/max" :dir :system))
(local (include-book "kestrel/arithmetic-light/min" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))

(local (include-book "internal/map-values-all-posp"))
(local (include-book "internal/intersect"))
(local (include-book "bag"))
(local (include-book "count"))
(local (include-book "cardinality"))
(local (include-book "extensionality"))
(local (include-book "subbag"))
(local (include-book "insert"))
(local (include-book "delete"))
(local (include-book "union"))
(local (include-book "sum"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl bagp-of-tree-intersect-of-fix-and-fix
  (bagp (tree-intersect (fix a) (fix b)))
  :enable (bagp
           treemap::mapp
           map-values-all-posp-when-tree-all-vals-posp
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define intersect ((a bagp)
                   (b bagp))
  :type-prescription :none
  :returns (bag bagp
                :hints (("Goal" :in-theory
                         (enable bagp-of-tree-intersect-of-fix-and-fix))))
  :parents (treebag)
  :short "Take the intersection of two @(see treebag)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "The count of each value in the result is the lesser of its counts in
       @('a') and @('b').")
    (xdoc::p
      "Time complexity: @($O(m\\log(n/m))$), where @($m \\leq n$) are the
       numbers of distinct elements of the two bags."))
  (tree-intersect (fix a) (fix b))
  :inline t
  :guard-hints (("Goal" :in-theory (enable bagp
                                           tree-all-vals-posp-of-fix
                                           treemap::treep-when-mapp-forward-chaining))))

;;;;;;;;;;;;;;;;;;;;

(defrule intersect-when-equiv-of-arg1-congruence
  (implies (equiv a0 a1)
           (equal (intersect a0 b)
                  (intersect a1 b)))
  :rule-classes :congruence
  :enable intersect)

(defrule intersect-when-equiv-of-arg2-congruence
  (implies (equiv b0 b1)
           (equal (intersect a b0)
                  (intersect a b1)))
  :rule-classes :congruence
  :enable intersect)

(defrule count-of-intersect
  (equal (count x (intersect a b))
         (acl2::min (count x a)
                    (count x b)))
  :enable (intersect
           count
           treemap::lookup
           treemap::keys
           treemap::mapp
           break-abstraction
           bagp-of-tree-intersect-of-fix-and-fix
           acl2::min))

;;;;;;;;;;;;;;;;;;;;

(defruled intersect-when-emptyp-of-arg1
  (implies (emptyp a)
           (equal (intersect a b)
                  (empty)))
  :enable (extensionality
           acl2::min))

(defrule intersect-when-emptyp-of-arg1-cheap
  (implies (emptyp a)
           (equal (intersect a b)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by intersect-when-emptyp-of-arg1)

(defrule intersect-of-empty
  (equal (intersect (empty) b)
         (empty))
  :enable intersect-when-emptyp-of-arg1)

(defruled intersect-when-emptyp-of-arg2
  (implies (emptyp b)
           (equal (intersect a b)
                  (empty)))
  :enable (extensionality
           acl2::min))

(defrule intersect-when-emptyp-of-arg2-cheap
  (implies (emptyp b)
           (equal (intersect a b)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by intersect-when-emptyp-of-arg2)

(defrule intersect-of-arg1-and-empty
  (equal (intersect a (empty))
         (empty))
  :enable intersect-when-emptyp-of-arg2)

(defrule emptyp-of-intersect-when-emptyp-of-arg1
  (implies (emptyp a)
           (emptyp (intersect a b)))
  :enable intersect-when-emptyp-of-arg1)

(defrule emptyp-of-intersect-when-emptyp-of-arg2
  (implies (emptyp b)
           (emptyp (intersect a b)))
  :enable intersect-when-emptyp-of-arg2)

;;;;;;;;;;;;;;;;;;;;

(defrule subbag-of-intersect0
  (implies (subbag a c)
           (subbag (intersect a b) c))
  :enable pick-a-point-polar)

(defrule subbag-of-intersect1
  (implies (subbag b c)
           (subbag (intersect a b) c))
  :enable pick-a-point-polar)

(defrule subbag-of-arg1-and-intersect0
  (equal (subbag a (intersect a b))
         (subbag a b))
  :enable (acl2::equal-of-booleans-cheap
           pick-a-point-polar))

(defrule subbag-of-arg1-and-intersect1
  (equal (subbag a (intersect b a))
         (subbag a b))
  :enable (acl2::equal-of-booleans-cheap
           pick-a-point-polar))

(defrule subbag-of-arg1-and-intersect
  (equal (subbag c (intersect a b))
         (and (subbag c a)
              (subbag c b)))
  :enable (acl2::equal-of-booleans-cheap
           pick-a-point-polar
           acl2::min))

(defrule monotonicity-of-intersect
  (implies (and (subbag a0 a1)
                (subbag b0 b1))
           (subbag (intersect a0 b0)
                   (intersect a1 b1)))
  :enable pick-a-point-polar)

;;;;;;;;;;;;;;;;;;;;

(defrule associativity-of-intersect
  (equal (intersect (intersect a b) c)
         (intersect a (intersect b c)))
  :enable extensionality)

(defrule commutativity-of-intersect
  (equal (intersect b a)
         (intersect a b))
  :enable extensionality)

(defrule commutativity-2-of-intersect
  (equal (intersect b (intersect a c))
         (intersect a (intersect b c)))
  :enable extensionality)

(defrule idempotence-of-intersect
  (equal (intersect a a)
         (fix a))
  :enable extensionality)

(defrule intersect-contraction
  (equal (intersect a (intersect a b))
         (intersect a b))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;

(defruled union-over-intersect
  (equal (union (intersect a b) c)
         (intersect (union a c) (union b c)))
  :enable (extensionality
           acl2::min
           acl2::max))

(defruled union-over-arg1-intersect
  (equal (union a (intersect b c))
         (intersect (union a b) (union a c)))
  :enable (extensionality
           acl2::min
           acl2::max))

(defrule intersect-over-union
  (equal (intersect (union a b) c)
         (union (intersect a c) (intersect b c)))
  :enable (extensionality
           acl2::min
           acl2::max))

(defrule intersect-over-arg1-and-union
  (equal (intersect a (union b c))
         (union (intersect a b) (intersect a c)))
  :enable (extensionality
           acl2::min
           acl2::max))

;;;;;;;;;;;;;;;;;;;;

(defruled intersect-when-subbag-arg1-arg2
  (implies (subbag a b)
           (equal (intersect a b)
                  (fix a)))
  :enable (extensionality
           acl2::min))

(defrule intersect-when-subbag-arg1-arg2-cheap
  (implies (subbag a b)
           (equal (intersect a b)
                  (fix a)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by intersect-when-subbag-arg1-arg2)

(defruled intersect-when-subbag-arg2-arg1
  (implies (subbag b a)
           (equal (intersect a b)
                  (fix b)))
  :enable (extensionality
           acl2::min))

(defrule intersect-when-subbag-arg2-arg1-cheap
  (implies (subbag b a)
           (equal (intersect a b)
                  (fix b)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by intersect-when-subbag-arg2-arg1)

;;;;;;;;;;;;;;;;;;;;

(defrule cardinality-of-intersect0-linear
  (<= (cardinality (intersect a b))
      (cardinality a))
  :rule-classes :linear
  :cases ((subbag (intersect a b) a)))

(defrule cardinality-of-intersect1-linear
  (<= (cardinality (intersect a b))
      (cardinality b))
  :rule-classes :linear
  :cases ((subbag (intersect a b) b)))

(defrule cardinality-of-intersect-when-not-subbag-linear
  (implies (not (subbag a b))
           (< (cardinality (intersect a b))
              (cardinality a)))
  :rule-classes :linear
  :use (:instance cardinality-when-proper-subbag-linear
                  (sub (intersect a b))
                  (sup a)))

(defrule equal-of-cardinality-of-intersect
  (equal (equal (cardinality (intersect a b)) (cardinality a))
         (subbag a b))
  :enable intersect-when-subbag-arg1-arg2)

(defrule <-of-cardinality-of-intersect
  (equal (< (cardinality (intersect a b)) (cardinality a))
         (not (subbag a b)))
  :enable intersect-when-subbag-arg1-arg2)

;;;;;;;;;;;;;;;;;;;;

(defrule sum-of-union-and-intersect
  (equal (sum (union a b) (intersect a b))
         (sum a b))
  :enable (extensionality
           acl2::max
           acl2::min))

(defrule cardinality-of-union
  (equal (cardinality (union a b))
         (- (+ (cardinality a) (cardinality b))
            (cardinality (intersect a b))))
  :use (cardinality-of-sum
        (:instance cardinality-of-sum
                   (a (union a b))
                   (b (intersect a b))))
  :disable cardinality-of-sum)

(defruled cardinality-of-intersect
  (equal (cardinality (intersect a b))
         (+ (cardinality a) (cardinality b)
            (- (cardinality (union a b))))))

(theory-invariant (incompatible! (:rewrite cardinality-of-union)
                                 (:rewrite cardinality-of-intersect)))

;;;;;;;;;;;;;;;;;;;;

(defruled intersect-of-insert
  (equal (intersect (insert x a) b)
         (if (< (count x a) (count x b))
             (insert x (intersect a b))
           (intersect a b)))
  :enable (extensionality
           count-of-insert
           acl2::min))

(defrule intersect-of-insert-when-count-<-count
  (implies (< (count x a) (count x b))
           (equal (intersect (insert x a) b)
                  (insert x (intersect a b))))
  :enable intersect-of-insert)

(defrule intersect-of-insert-when-count-<=-count
  (implies (<= (count x b) (count x a))
           (equal (intersect (insert x a) b)
                  (intersect a b)))
  :enable intersect-of-insert)

(defruled intersect-of-arg1-and-insert
  (equal (intersect a (insert x b))
         (if (< (count x b) (count x a))
             (insert x (intersect a b))
           (intersect a b)))
  :enable (extensionality
           count-of-insert
           acl2::min))

(defrule intersect-of-arg1-and-insert-when-count-<-count
  (implies (< (count x b) (count x a))
           (equal (intersect a (insert x b))
                  (insert x (intersect a b))))
  :enable intersect-of-arg1-and-insert)

(defrule intersect-of-arg1-and-insert-when-count-<=-count
  (implies (<= (count x a) (count x b))
           (equal (intersect a (insert x b))
                  (intersect a b)))
  :enable intersect-of-arg1-and-insert)

(defruled intersect-of-delete
  (equal (intersect (delete x a) b)
         (if (<= (count x a) (count x b))
             (delete x (intersect a b))
           (intersect a b)))
  :enable (extensionality
           count-of-delete
           acl2::min
           nfix))

(defrule intersect-of-delete-when-count-<=-count
  (implies (<= (count x a) (count x b))
           (equal (intersect (delete x a) b)
                  (delete x (intersect a b))))
  :enable intersect-of-delete)

(defrule intersect-of-delete-when-count-<-count
  (implies (< (count x b) (count x a))
           (equal (intersect (delete x a) b)
                  (intersect a b)))
  :enable intersect-of-delete)

(defruled intersect-of-arg1-and-delete
  (equal (intersect a (delete x b))
         (if (<= (count x b) (count x a))
             (delete x (intersect a b))
           (intersect a b)))
  :enable (extensionality
           count-of-delete
           acl2::min
           nfix))

(defrule intersect-of-arg1-and-delete-when-count-<=-count
  (implies (<= (count x b) (count x a))
           (equal (intersect a (delete x b))
                  (delete x (intersect a b))))
  :enable intersect-of-arg1-and-delete)

(defrule intersect-of-arg1-and-delete-when-count-<-count
  (implies (< (count x a) (count x b))
           (equal (intersect a (delete x b))
                  (intersect a b)))
  :enable intersect-of-arg1-and-delete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy intersect-extra-rules
  '(intersect-of-insert
    intersect-of-arg1-and-insert
    intersect-of-delete
    intersect-of-arg1-and-delete
    ))
