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

(include-book "internal/union-defs")
(include-book "bag-defs")
(include-book "count-defs")
(include-book "subbag-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/arithmetic-light/max" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))

(local (include-book "internal/map-values-all-posp"))
(local (include-book "internal/union"))
(local (include-book "bag"))
(local (include-book "count"))
(local (include-book "extensionality"))
(local (include-book "subbag"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

;; Disabled, so that a natural is derived from a positive only where enabled.
(defruledl natp-when-posp
  (implies (posp x)
           (natp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define union ((a bagp)
               (b bagp))
  :type-prescription :none
  :returns (bag bagp
                :hints (("Goal" :in-theory (enable* bagp
                                                    break-abstraction))))
  :parents (treebag)
  :short "Take the union of two @(see treebag)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "The count of each value in the result is the greater of its counts in
       @('a') and @('b').")
    (xdoc::p
      "Time complexity: @($O(m\\log(n/m))$), where @($m \\leq n$) are the
       numbers of distinct elements of the two bags."))
  (map-union (fix a) (fix b))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule union-when-equiv-of-arg1-congruence
  (implies (equiv a0 a1)
           (equal (union a0 b)
                  (union a1 b)))
  :rule-classes :congruence
  :enable union)

(defrule union-when-equiv-of-arg2-congruence
  (implies (equiv b0 b1)
           (equal (union a b0)
                  (union a b1)))
  :rule-classes :congruence
  :enable union)

(defrule count-of-union
  (equal (count x (union a b))
         (acl2::max (count x a)
                    (count x b)))
  :enable (union
           count
           bagp
           break-abstraction
           natp-when-posp
           acl2::acl2-numberp-when-natp
           acl2::<=-of-0-when-natp
           acl2::max-when-<=-1
           acl2::max-when-<=-2))

(defrule emptyp-of-union
  (equal (emptyp (union a b))
         (and (emptyp a)
              (emptyp b)))
  :enable (union
           emptyp
           bagp
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;

(defrule subbag-of-arg1-and-union0
  (subbag a (union a b))
  :enable pick-a-point)

(defrule subbag-of-arg1-and-union1
  (subbag a (union b a))
  :enable pick-a-point)

(defrule subbag-of-union0
  (equal (subbag (union a b) a)
         (subbag b a))
  :enable (acl2::equal-of-booleans-cheap
           pick-a-point-polar))

(defrule subbag-of-union1
  (equal (subbag (union a b) b)
         (subbag a b))
  :enable (acl2::equal-of-booleans-cheap
           pick-a-point-polar))

(defrule monotonicity-of-union
  (implies (and (subbag a0 a1)
                (subbag b0 b1))
           (subbag (union a0 b0)
                   (union a1 b1)))
  :enable pick-a-point-polar)

;;;;;;;;;;;;;;;;;;;;

(defrule associativity-of-union
  (equal (union (union a b) c)
         (union a (union b c)))
  :enable extensionality)

(defrule commutativity-of-union
  (equal (union b a)
         (union a b))
  :enable extensionality)

(defrule commutativity-2-of-union
  (equal (union b (union a c))
         (union a (union b c)))
  :enable extensionality)

(defrule idempotence-of-union
  (equal (union a a)
         (fix a))
  :enable extensionality)

(defrule union-contraction
  (equal (union a (union a b))
         (union a b))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;

(defruled union-when-emptyp-of-arg1
  (implies (emptyp a)
           (equal (union a b)
                  (fix b)))
  :enable (extensionality
           acl2::max-when-<=-1))

(defrule union-when-emptyp-of-arg1-cheap
  (implies (emptyp a)
           (equal (union a b)
                  (fix b)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by union-when-emptyp-of-arg1)

(defrule union-of-empty
  (equal (union (empty) b)
         (fix b))
  :enable union-when-emptyp-of-arg1)

(defruled union-when-emptyp-of-arg2
  (implies (emptyp b)
           (equal (union a b)
                  (fix a)))
  :enable (extensionality
           acl2::max-when-<=-2))

(defrule union-when-emptyp-of-arg2-cheap
  (implies (emptyp b)
           (equal (union a b)
                  (fix a)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by union-when-emptyp-of-arg2)

(defrule union-of-arg1-and-empty
  (equal (union a (empty))
         (fix a))
  :enable union-when-emptyp-of-arg2)

;;;;;;;;;;;;;;;;;;;;

(defruled union-when-subbag-arg1-arg2
  (implies (subbag a b)
           (equal (union a b)
                  (fix b)))
  :enable (extensionality
           acl2::max-when-<=-1))

(defrule union-when-subbag-arg1-arg2-cheap
  (implies (subbag a b)
           (equal (union a b)
                  (fix b)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by union-when-subbag-arg1-arg2)

(defruled union-when-subbag-arg2-arg1
  (implies (subbag b a)
           (equal (union a b)
                  (fix a)))
  :enable (extensionality
           acl2::max-when-<=-2))

(defrule union-when-subbag-arg2-arg1-cheap
  (implies (subbag b a)
           (equal (union a b)
                  (fix a)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by union-when-subbag-arg2-arg1)
