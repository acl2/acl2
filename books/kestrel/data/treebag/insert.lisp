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

(include-book "kestrel/utilities/arith-fix-and-equiv-defs" :dir :system)

(include-book "kestrel/data/treemap/update-defs" :dir :system)

(include-book "bag-defs")
(include-book "count-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))

(local (include-book "kestrel/data/treemap/update" :dir :system))

(local (include-book "bag"))
(local (include-book "count"))
(local (include-book "extensionality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert-many (x (n natp) (bag bagp))
  (declare (xargs :type-prescription :none))
  :returns (bag$ bagp
                 :hints (("Goal" :in-theory (enable* break-abstraction
                                                     nat-equiv))))
  :parents (treebag)
  :short "Add some number of occurrences of a value to a @(see treebag)."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(\\log(m))$), where @($m$) is the number of distinct
     elements of the bag.")
  (if (fast-nat-equiv n 0)
      (fix bag)
    (treemap::update x (+ (lnfix n) (count x bag)) (fix bag)))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule insert-many-when-equiv-congruence
  (implies (equiv bag0 bag1)
           (equal (insert-many x n bag0)
                  (insert-many x n bag1)))
  :rule-classes :congruence
  :enable insert-many)

(defrule insert-many-when-nat-equiv-congruence
  (implies (nat-equiv n0 n1)
           (equal (insert-many x n0 bag)
                  (insert-many x n1 bag)))
  :rule-classes :congruence
  :enable insert-many)

(defruled count-of-insert-many
  (equal (count y (insert-many x n bag))
         (if (equal y x)
             (+ (nfix n) (count y bag))
           (count y bag)))
  :enable (insert-many
           break-abstraction
           nat-equiv))

(defrule count-of-insert-many-when-equal
  (equal (count x (insert-many x n bag))
         (+ (nfix n) (count x bag)))
  :enable count-of-insert-many)

(defruled count-of-insert-many-when-not-equal
  (implies (not (equal x y))
           (equal (count y (insert-many x n bag))
                  (count y bag)))
  :enable count-of-insert-many)

(defrule count-of-insert-many-when-not-equal-cheap
  (implies (not (equal x y))
           (equal (count y (insert-many x n bag))
                  (count y bag)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by count-of-insert-many-when-not-equal)

(defrule emptyp-of-insert-many
  (equal (emptyp (insert-many x n bag))
         (and (equal (nfix n) 0)
              (emptyp bag)))
  :enable (insert-many
           emptyp
           break-abstraction
           nat-equiv))

(defrule insert-many-of-0
  (equal (insert-many x 0 bag)
         (fix bag))
  :enable insert-many)

(defrule insert-many-of-arg1-and-insert-many
  (equal (insert-many x m (insert-many x n bag))
         (insert-many x (+ (nfix m) (nfix n)) bag))
  :enable (extensionality
           count-of-insert-many))

(defrule commutativity-of-insert-many
  (equal (insert-many y m (insert-many x n bag))
         (insert-many x n (insert-many y m bag)))
  :enable (extensionality
           count-of-insert-many))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert (x (bag bagp))
  (declare (xargs :type-prescription :none))
  :returns (bag$ bagp)
  :parents (treebag)
  :short "Add an occurrence of a value to a @(see treebag)."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(\\log(m))$), where @($m$) is the number of distinct
     elements of the bag.")
  (mbe :logic (insert-many x 1 bag)
       :exec (treemap::update x (+ 1 (count x bag)) (fix bag)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* insert-many
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule insert-when-equiv-congruence
  (implies (equiv bag0 bag1)
           (equal (insert x bag0)
                  (insert x bag1)))
  :rule-classes :congruence
  :enable insert)

(defruled count-of-insert
  (equal (count y (insert x bag))
         (if (equal y x)
             (+ 1 (count y bag))
           (count y bag)))
  :enable (insert
           count-of-insert-many))

(defrule count-of-insert-when-equal
  (equal (count x (insert x bag))
         (+ 1 (count x bag)))
  :enable insert)

(defruled count-of-insert-when-not-equal
  (implies (not (equal x y))
           (equal (count y (insert x bag))
                  (count y bag)))
  :enable insert)

(defrule count-of-insert-when-not-equal-cheap
  (implies (not (equal x y))
           (equal (count y (insert x bag))
                  (count y bag)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by count-of-insert-when-not-equal)

(defrule emptyp-of-insert
  (not (emptyp (insert x bag)))
  :enable insert)

(defrule commutativity-of-insert
  (equal (insert y (insert x bag))
         (insert x (insert y bag)))
  :enable (extensionality
           count-of-insert))

(defrule insert-many-of-insert
  (equal (insert-many x n (insert y bag))
         (insert y (insert-many x n bag)))
  :enable (extensionality
           count-of-insert-many
           count-of-insert))

(defruled insert-of-insert-many-becomes-insert-many
  (equal (insert x (insert-many x n bag))
         (insert-many x (+ (nfix n) 1) bag))
  :enable (extensionality
           count-of-insert-many
           count-of-insert))

;;;;;;;;;;;;;;;;;;;;

;; The normal form for a single occurrence is insert. This must come after
;; every proof that enables insert, since the two would loop.

(defrule insert-many-of-1
  (equal (insert-many x 1 bag)
         (insert x bag))
  :enable insert)

(theory-invariant (incompatible! (:definition insert$inline)
                                 (:rewrite insert-many-of-1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy insert-extra-rules
  '(count-of-insert-many
    count-of-insert
    ))
