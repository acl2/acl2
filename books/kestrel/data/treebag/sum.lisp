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

(include-book "internal/sum-defs")
(include-book "bag-defs")
(include-book "count-defs")
(include-book "insert-defs")
(include-book "delete-defs")
(include-book "cardinality-defs")
(include-book "subbag-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))

(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/min-max" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))

(local (include-book "internal/map-values-all-posp"))
(local (include-book "internal/induction"))
(local (include-book "internal/sum"))
(local (include-book "bag"))
(local (include-book "count"))
(local (include-book "cardinality"))
(local (include-book "extensionality"))
(local (include-book "insert"))
(local (include-book "delete"))
(local (include-book "subbag"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

;; Disabled, so that a natural is derived from a positive only where enabled.
(defruledl natp-when-posp
  (implies (posp x)
           (natp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sum ((a bagp)
             (b bagp))
  :type-prescription :none
  :returns (bag bagp
                :hints (("Goal" :in-theory (enable* bagp
                                                    break-abstraction))))
  :parents (treebag)
  :short "Add the occurrences of two @(see treebag)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "The count of each value in the result is the sum of its counts in
       @('a') and @('b').")
    (xdoc::p
      "Time complexity: @($O(m\\log(n/m))$), where @($m \\leq n$) are the
       numbers of distinct elements of the two bags."))
  (map-sum (fix a) (fix b))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule sum-when-equiv-of-arg1-congruence
  (implies (equiv a0 a1)
           (equal (sum a0 b)
                  (sum a1 b)))
  :rule-classes :congruence
  :enable sum)

(defrule sum-when-equiv-of-arg2-congruence
  (implies (equiv b0 b1)
           (equal (sum a b0)
                  (sum a b1)))
  :rule-classes :congruence
  :enable sum)

(defrule count-of-sum
  (equal (count x (sum a b))
         (+ (count x a)
            (count x b)))
  :enable (sum
           count
           bagp
           break-abstraction
           natp-when-posp
           acl2::acl2-numberp-when-natp))

;;;;;;;;;;;;;;;;;;;;

(defruled sum-when-emptyp-of-arg1
  (implies (emptyp a)
           (equal (sum a b)
                  (fix b)))
  :enable extensionality)

(defrule sum-when-emptyp-of-arg1-cheap
  (implies (emptyp a)
           (equal (sum a b)
                  (fix b)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by sum-when-emptyp-of-arg1)

(defrule sum-of-empty
  (equal (sum (empty) b)
         (fix b))
  :enable sum-when-emptyp-of-arg1)

(defruled sum-when-emptyp-of-arg2
  (implies (emptyp b)
           (equal (sum a b)
                  (fix a)))
  :enable extensionality)

(defrule sum-when-emptyp-of-arg2-cheap
  (implies (emptyp b)
           (equal (sum a b)
                  (fix a)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by sum-when-emptyp-of-arg2)

(defrule sum-of-arg1-and-empty
  (equal (sum a (empty))
         (fix a))
  :enable sum-when-emptyp-of-arg2)

;;;;;;;;;;;;;;;;;;;;

(defrule associativity-of-sum
  (equal (sum (sum a b) c)
         (sum a (sum b c)))
  :enable extensionality)

(defrule commutativity-of-sum
  (equal (sum b a)
         (sum a b))
  :enable extensionality)

(defrule commutativity-2-of-sum
  (equal (sum b (sum a c))
         (sum a (sum b c)))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;

;; Inserts float outside sums.

(defrule sum-of-insert-many
  (equal (sum (insert-many x n a) b)
         (insert-many x n (sum a b)))
  :enable (extensionality
           count-of-insert-many))

(defrule sum-of-arg1-and-insert-many
  (equal (sum a (insert-many x n b))
         (insert-many x n (sum a b)))
  :enable (extensionality
           count-of-insert-many))

(defrule sum-of-insert
  (equal (sum (insert x a) b)
         (insert x (sum a b)))
  :enable (extensionality
           count-of-insert))

(defrule sum-of-arg1-and-insert
  (equal (sum a (insert x b))
         (insert x (sum a b)))
  :enable (extensionality
           count-of-insert))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The cardinality takes an induction, which removes every occurrence of the
;; first bag's smallest element at each step. Removing an element from the
;; first bag removes as many occurrences from the sum.

(defruledl sum-of-treemap-delete
  (equal (sum (treemap::delete x (fix a)) b)
         (delete-many x (count x a) (sum a b)))
  :enable (extensionality
           break-abstraction
           count-of-delete-many
           nfix))

(defrule cardinality-of-sum
  (equal (cardinality (sum a b))
         (+ (cardinality a)
            (cardinality b)))
  :induct (min-delete-induction a)
  :enable (break-abstraction
           sum-of-treemap-delete
           nfix)
  :disable fix-when-bagp)

(defrule emptyp-of-sum
  (equal (emptyp (sum a b))
         (and (emptyp a)
              (emptyp b)))
  :enable emptyp-becomes-equal-of-cardinality-and-0)

;;;;;;;;;;;;;;;;;;;;

(defrule subbag-of-arg1-and-sum0
  (subbag a (sum a b))
  :enable pick-a-point)

(defrule subbag-of-arg1-and-sum1
  (subbag a (sum b a))
  :enable pick-a-point)

(defrule subbag-of-sum0
  (equal (subbag (sum a b) a)
         (emptyp b))
  :use (:instance cardinality-when-subbag-linear
                  (sub (sum a b))
                  (sup a))
  :enable emptyp-becomes-equal-of-cardinality-and-0)

(defrule subbag-of-sum1
  (equal (subbag (sum a b) b)
         (emptyp a))
  :use (:instance cardinality-when-subbag-linear
                  (sub (sum a b))
                  (sup b))
  :enable emptyp-becomes-equal-of-cardinality-and-0)

(defrule monotonicity-of-sum
  (implies (and (subbag a0 a1)
                (subbag b0 b1))
           (subbag (sum a0 b0)
                   (sum a1 b1)))
  :enable pick-a-point-polar)
