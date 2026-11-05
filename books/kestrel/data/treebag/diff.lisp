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

(include-book "internal/diff-defs")
(include-book "bag-defs")
(include-book "count-defs")
(include-book "cardinality-defs")
(include-book "subbag-defs")
(include-book "union-defs")
(include-book "intersect-defs")
(include-book "sum-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/max" :dir :system))
(local (include-book "kestrel/arithmetic-light/min" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))

(local (include-book "internal/map-values-all-posp"))
(local (include-book "internal/diff"))
(local (include-book "bag"))
(local (include-book "count"))
(local (include-book "cardinality"))
(local (include-book "extensionality"))
(local (include-book "subbag"))
(local (include-book "union"))
(local (include-book "intersect"))
(local (include-book "sum"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl bagp-of-tree-diff-of-fix-and-fix
  (bagp (tree-diff (fix a) (fix b)))
  :enable (bagp
           treemap::mapp
           map-values-all-posp-when-tree-all-vals-posp
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define diff ((a bagp)
              (b bagp))
  :type-prescription :none
  :returns (bag bagp
                :hints (("Goal" :in-theory
                         (enable bagp-of-tree-diff-of-fix-and-fix))))
  :parents (treebag)
  :short "Take the difference of two @(see treebag)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "The count of each value in the result is its count in @('a') less its
       count in @('b'), or zero if @('b') has at least as many.")
    (xdoc::p
      "Time complexity: @($O(m\\log(n/m))$), where @($m \\leq n$) are the
       numbers of distinct elements of the two bags."))
  (tree-diff (fix a) (fix b))
  :inline t
  :guard-hints (("Goal" :in-theory (enable bagp
                                           tree-all-vals-posp-of-fix
                                           treemap::treep-when-mapp-forward-chaining))))

;;;;;;;;;;;;;;;;;;;;

(defrule diff-when-equiv-of-arg1-congruence
  (implies (equiv a0 a1)
           (equal (diff a0 b)
                  (diff a1 b)))
  :rule-classes :congruence
  :enable diff)

(defrule diff-when-equiv-of-arg2-congruence
  (implies (equiv b0 b1)
           (equal (diff a b0)
                  (diff a b1)))
  :rule-classes :congruence
  :enable diff)

(defrule count-of-diff
  (equal (count x (diff a b))
         (nfix (- (count x a)
                  (count x b))))
  :enable (diff
           count
           treemap::lookup
           treemap::keys
           treemap::mapp
           break-abstraction
           bagp-of-tree-diff-of-fix-and-fix
           nfix
           acl2::integerp-when-posp
           acl2::acl2-numberp-when-posp))

;;;;;;;;;;;;;;;;;;;;

(defruled diff-when-emptyp-of-arg1
  (implies (emptyp a)
           (equal (diff a b)
                  (empty)))
  :enable (extensionality
           nfix))

(defrule diff-when-emptyp-of-arg1-cheap
  (implies (emptyp a)
           (equal (diff a b)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by diff-when-emptyp-of-arg1)

(defrule diff-of-empty
  (equal (diff (empty) b)
         (empty))
  :enable diff-when-emptyp-of-arg1)

(defruled diff-when-emptyp-of-arg2
  (implies (emptyp b)
           (equal (diff a b)
                  (fix a)))
  :enable (extensionality
           nfix))

(defrule diff-when-emptyp-of-arg2-cheap
  (implies (emptyp b)
           (equal (diff a b)
                  (fix a)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by diff-when-emptyp-of-arg2)

(defrule diff-of-arg1-and-empty
  (equal (diff a (empty))
         (fix a))
  :enable diff-when-emptyp-of-arg2)

(defrule diff-of-arg1-and-arg1
  (equal (diff a a)
         (empty))
  :enable (extensionality
           nfix))

;;;;;;;;;;;;;;;;;;;;

(defrule subbag-of-diff
  (implies (subbag a c)
           (subbag (diff a b) c))
  :enable (pick-a-point-polar
           nfix))

;; Monotonic on arg1, antitonic on arg2
(defrule monotonicity-of-diff
  (implies (and (subbag a0 a1)
                (subbag b1 b0))
           (subbag (diff a0 b0)
                   (diff a1 b1)))
  :enable (pick-a-point-polar
           nfix))

(defruled subbag-of-diff-becomes-subbag-of-sum
  (equal (subbag (diff a b) c)
         (subbag a (sum b c)))
  :use (:instance count-<=-count-when-subbag-linear
                  (x (subbag-sk-witness a (sum b c)))
                  (sub (diff a b))
                  (sup c))
  :enable (acl2::equal-of-booleans-cheap
           pick-a-point-polar
           nfix))

;;;;;;;;;;;;;;;;;;;;

(defrule diff-of-union
  (equal (diff (union a b) c)
         (union (diff a c) (diff b c)))
  :enable (extensionality
           nfix
           acl2::max))

(defrule diff-of-arg1-and-union
  (equal (diff a (union b c))
         (intersect (diff a b) (diff a c)))
  :enable (extensionality
           nfix
           acl2::max
           acl2::min))

(defrule diff-of-intersect
  (equal (diff (intersect a b) c)
         (intersect (diff a c) (diff b c)))
  :enable (extensionality
           nfix
           acl2::min))

(defrule diff-of-arg1-and-intersect
  (equal (diff a (intersect b c))
         (union (diff a b) (diff a c)))
  :enable (extensionality
           nfix
           acl2::max
           acl2::min))

;;;;;;;;;;;;;;;;;;;;

(defrule diff-of-diff
  (equal (diff (diff a b) c)
         (diff a (sum b c)))
  :enable (extensionality
           nfix))

(defrule diff-of-sum-and-arg1
  (equal (diff (sum a b) a)
         (fix b))
  :enable (extensionality
           nfix))

(defrule diff-of-sum-and-arg2
  (equal (diff (sum a b) b)
         (fix a))
  :enable (extensionality
           nfix))

(defrule sum-of-arg1-and-diff
  (equal (sum a (diff b a))
         (union a b))
  :enable (extensionality
           nfix
           acl2::max))

(defrule sum-of-diff-and-arg2
  (equal (sum (diff b a) a)
         (union b a))
  :enable (extensionality
           nfix
           acl2::max))

(defrule sum-of-diff-and-intersect
  (equal (sum (diff a b) (intersect a b))
         (fix a))
  :enable (extensionality
           nfix
           acl2::min))

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-diff
  (equal (emptyp (diff a b))
         (subbag a b))
  :use (:instance subbag-of-diff-becomes-subbag-of-sum
                  (c (empty))))

(defrule cardinality-of-diff
  (equal (cardinality (diff a b))
         (- (cardinality a)
            (cardinality (intersect a b))))
  :use (:instance cardinality-of-sum
                  (a (diff a b))
                  (b (intersect a b)))
  :disable cardinality-of-sum)
