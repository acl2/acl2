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
(include-book "kestrel/data/treemap/delete-defs" :dir :system)

(include-book "bag-defs")
(include-book "count-defs")
(include-book "insert-defs")
(include-book "cardinality-defs")
(include-book "subbag-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "bag"))
(local (include-book "count"))
(local (include-book "cardinality"))
(local (include-book "extensionality"))
(local (include-book "subbag"))
(local (include-book "insert"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-many (x (n natp) (bag bagp))
  (declare (xargs :type-prescription :none))
  :returns (bag$ bagp
                 :hints (("Goal" :in-theory (enable* break-abstraction
                                                     posp))))
  :parents (treebag)
  :short "Remove some number of occurrences of a value from a @(see
          treebag)."
  :long
  (xdoc::topstring
    (xdoc::p
      "If the bag has fewer occurrences than requested, all of them are
       removed.")
    (xdoc::p
      "Time complexity: @($O(\\log(m))$), where @($m$) is the number of
       distinct elements of the bag."))
  (let ((c (count x bag))
        (n (lnfix n)))
    (if (<= c n)
        (treemap::delete x (fix bag))
      (treemap::update x (- c n) (fix bag))))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule delete-many-when-equiv-congruence
  (implies (equiv bag0 bag1)
           (equal (delete-many x n bag0)
                  (delete-many x n bag1)))
  :rule-classes :congruence
  :enable delete-many)

(defrule delete-many-when-nat-equiv-congruence
  (implies (nat-equiv n0 n1)
           (equal (delete-many x n0 bag)
                  (delete-many x n1 bag)))
  :rule-classes :congruence
  :enable delete-many)

(defruled count-of-delete-many
  (equal (count y (delete-many x n bag))
         (if (equal y x)
             (nfix (- (count y bag) (nfix n)))
           (count y bag)))
  :enable (delete-many
           break-abstraction
           nfix
           posp))

(defrule count-of-delete-many-when-equal
  (equal (count x (delete-many x n bag))
         (nfix (- (count x bag) (nfix n))))
  :enable count-of-delete-many)

(defruled count-of-delete-many-when-not-equal
  (implies (not (equal x y))
           (equal (count y (delete-many x n bag))
                  (count y bag)))
  :enable count-of-delete-many)

(defrule count-of-delete-many-when-not-equal-cheap
  (implies (not (equal x y))
           (equal (count y (delete-many x n bag))
                  (count y bag)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by count-of-delete-many-when-not-equal)

(defrule delete-many-of-0
  (equal (delete-many x 0 bag)
         (fix bag))
  :enable (extensionality
           count-of-delete-many))

(defruled delete-many-when-count-0
  (implies (equal (count x bag) 0)
           (equal (delete-many x n bag)
                  (fix bag)))
  :enable (extensionality
           count-of-delete-many
           nfix))

(defrule delete-many-when-count-0-cheap
  (implies (equal (count x bag) 0)
           (equal (delete-many x n bag)
                  (fix bag)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by delete-many-when-count-0)

;; The removal takes either every occurrence or exactly n of them.

(defruled cardinality-of-delete-many
  (equal (cardinality (delete-many x n bag))
         (if (<= (count x bag) (nfix n))
             (- (cardinality bag) (count x bag))
           (- (cardinality bag) (nfix n))))
  :enable (delete-many
           break-abstraction
           posp))

(defrule cardinality-of-delete-many-when-count-<=
  (implies (<= (count x bag) (nfix n))
           (equal (cardinality (delete-many x n bag))
                  (- (cardinality bag) (count x bag))))
  :enable cardinality-of-delete-many)

(defrule cardinality-of-delete-many-when-<=-count
  (implies (<= (nfix n) (count x bag))
           (equal (cardinality (delete-many x n bag))
                  (- (cardinality bag) (nfix n))))
  :enable cardinality-of-delete-many)

(defrule cardinality-of-delete-many-<=-cardinality-linear
  (<= (cardinality (delete-many x n bag))
      (cardinality bag))
  :rule-classes :linear
  :enable cardinality-of-delete-many)

(defrule cardinality-of-delete-many-<-cardinality-linear
  (implies (and (not (equal (count x bag) 0))
                (not (nat-equiv n 0)))
           (< (cardinality (delete-many x n bag))
              (cardinality bag)))
  :rule-classes :linear
  :enable (cardinality-of-delete-many
           nat-equiv))

;; Removing up to n occurrences of x empties a bag exactly when x is its only
;; element and occurs at most n times.

(defrule emptyp-of-delete-many
  (equal (emptyp (delete-many x n bag))
         (and (<= (count x bag) (nfix n))
              (equal (cardinality bag) (count x bag))))
  :enable (emptyp-becomes-equal-of-cardinality-and-0
           cardinality-of-delete-many))

(defrule subbag-of-delete-many
  (subbag (delete-many x n bag) bag)
  :enable (pick-a-point
           count-of-delete-many
           nfix))

(defrule subbag-of-arg1-and-delete-many
  (equal (subbag bag (delete-many x n bag))
         (or (equal (nfix n) 0)
             (equal (count x bag) 0)))
  :enable (acl2::equal-of-booleans-cheap
           pick-a-point-polar
           count-of-delete-many
           nfix))

(defrule monotonicity-of-delete-many
  (implies (subbag sub sup)
           (subbag (delete-many x n sub)
                   (delete-many x n sup)))
  :enable (pick-a-point-polar
           count-of-delete-many
           nfix))

(defrule delete-many-of-arg1-and-delete-many
  (equal (delete-many x m (delete-many x n bag))
         (delete-many x (+ (nfix m) (nfix n)) bag))
  :enable (extensionality
           count-of-delete-many
           nfix))

;; The loop-stopper sorts by element alone. The default one would compare
;; multiplicities first, which can keep two occurrences of an element apart.

(defrule commutativity-of-delete-many
  (equal (delete-many y m (delete-many x n bag))
         (delete-many x n (delete-many y m bag)))
  :rule-classes ((:rewrite :loop-stopper ((y x))))
  :enable (extensionality
           count-of-delete-many
           nfix))

;; Removing occurrences just inserted cancels them, leaving whichever of the
;; insertion and the removal was larger.

(defruled delete-many-of-arg1-and-insert-many
  (equal (delete-many x m (insert-many x n bag))
         (if (<= (nfix m) (nfix n))
             (insert-many x (- (nfix n) (nfix m)) bag)
           (delete-many x (- (nfix m) (nfix n)) bag)))
  :enable (extensionality
           count-of-delete-many
           count-of-insert-many
           nfix))

(defruled delete-many-of-insert-many-when-not-equal
  (implies (not (equal x y))
           (equal (delete-many x m (insert-many y n bag))
                  (insert-many y n (delete-many x m bag))))
  :enable (extensionality
           count-of-delete-many
           count-of-insert-many))

(defrule delete-many-of-insert-many-when-not-equal-cheap
  (implies (not (equal x y))
           (equal (delete-many x m (insert-many y n bag))
                  (insert-many y n (delete-many x m bag))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by delete-many-of-insert-many-when-not-equal)

(defrule insert-many-of-delete-many-same
  (implies (<= (nfix n) (count x bag))
           (equal (insert-many x n (delete-many x n bag))
                  (fix bag)))
  :enable (extensionality
           count-of-delete-many
           count-of-insert-many
           nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete (x (bag bagp))
  (declare (xargs :type-prescription :none))
  :returns (bag$ bagp)
  :parents (treebag)
  :short "Remove an occurrence of a value from a @(see treebag)."
  :long
  (xdoc::topstring
    (xdoc::p
      "If the value does not occur in the bag, the bag is unchanged.")
    (xdoc::p
      "Time complexity: @($O(\\log(m))$), where @($m$) is the number of
       distinct elements of the bag."))
  (mbe :logic (delete-many x 1 bag)
       :exec (let ((c (count x bag)))
               (if (<= c 1)
                   (treemap::delete x (fix bag))
                 (treemap::update x (- c 1) (fix bag)))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* delete-many
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule delete-when-equiv-congruence
  (implies (equiv bag0 bag1)
           (equal (delete x bag0)
                  (delete x bag1)))
  :rule-classes :congruence
  :enable delete)

(defruled count-of-delete
  (equal (count y (delete x bag))
         (if (equal y x)
             (nfix (- (count y bag) 1))
           (count y bag)))
  :enable (delete
           count-of-delete-many))

(defrule count-of-delete-when-equal
  (equal (count x (delete x bag))
         (nfix (- (count x bag) 1)))
  :enable delete)

(defruled count-of-delete-when-not-equal
  (implies (not (equal x y))
           (equal (count y (delete x bag))
                  (count y bag)))
  :enable delete)

(defrule count-of-delete-when-not-equal-cheap
  (implies (not (equal x y))
           (equal (count y (delete x bag))
                  (count y bag)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by count-of-delete-when-not-equal)

(defruled delete-when-count-0
  (implies (equal (count x bag) 0)
           (equal (delete x bag)
                  (fix bag)))
  :enable (delete
           delete-many-when-count-0))

(defrule delete-when-count-0-cheap
  (implies (equal (count x bag) 0)
           (equal (delete x bag)
                  (fix bag)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by delete-when-count-0)

(defruled cardinality-of-delete
  (equal (cardinality (delete x bag))
         (if (equal (count x bag) 0)
             (cardinality bag)
           (- (cardinality bag) 1)))
  :enable (delete
           cardinality-of-delete-many))

(defrule cardinality-of-delete-when-count-0
  (implies (equal (count x bag) 0)
           (equal (cardinality (delete x bag))
                  (cardinality bag)))
  :enable cardinality-of-delete)

(defrule cardinality-of-delete-when-count-nonzero
  (implies (not (equal (count x bag) 0))
           (equal (cardinality (delete x bag))
                  (- (cardinality bag) 1)))
  :enable cardinality-of-delete)

(defrule cardinality-of-delete-<=-cardinality-linear
  (<= (cardinality (delete x bag))
      (cardinality bag))
  :rule-classes :linear
  :enable cardinality-of-delete)

(defrule cardinality-of-delete-<-cardinality-linear
  (implies (not (equal (count x bag) 0))
           (< (cardinality (delete x bag))
              (cardinality bag)))
  :rule-classes :linear
  :enable cardinality-of-delete)

(defrule emptyp-of-delete
  (equal (emptyp (delete x bag))
         (and (<= (count x bag) 1)
              (equal (cardinality bag) (count x bag))))
  :enable delete)

(defrule subbag-of-delete
  (subbag (delete x bag) bag)
  :enable (pick-a-point
           count-of-delete
           nfix))

(defrule subbag-of-arg1-and-delete
  (equal (subbag bag (delete x bag))
         (equal (count x bag) 0))
  :enable (acl2::equal-of-booleans-cheap
           pick-a-point-polar
           count-of-delete
           nfix))

(defrule monotonicity-of-delete
  (implies (subbag sub sup)
           (subbag (delete x sub)
                   (delete x sup)))
  :enable (pick-a-point-polar
           count-of-delete
           nfix))

(defrule commutativity-of-delete
  (equal (delete y (delete x bag))
         (delete x (delete y bag)))
  :enable (extensionality
           count-of-delete))

(defruled delete-of-insert
  (equal (delete x (insert y bag))
         (if (equal x y)
             (fix bag)
           (insert y (delete x bag))))
  :enable (extensionality
           count-of-delete
           count-of-insert))

(defrule delete-of-insert-same
  (equal (delete x (insert x bag))
         (fix bag))
  :enable delete-of-insert)

(defruled delete-of-insert-when-not-equal
  (implies (not (equal x y))
           (equal (delete x (insert y bag))
                  (insert y (delete x bag))))
  :by delete-of-insert)

(defrule delete-of-insert-when-not-equal-cheap
  (implies (not (equal x y))
           (equal (delete x (insert y bag))
                  (insert y (delete x bag))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by delete-of-insert-when-not-equal)

(defrule insert-of-delete-same
  (implies (not (equal (count x bag) 0))
           (equal (insert x (delete x bag))
                  (fix bag)))
  :enable (extensionality
           count-of-delete
           count-of-insert))

(defruled delete-of-arg1-and-insert-many
  (equal (delete x (insert-many x n bag))
         (if (equal (nfix n) 0)
             (delete x bag)
           (insert-many x (- (nfix n) 1) bag)))
  :enable (extensionality
           count-of-delete
           count-of-insert-many
           nfix))

(defruled delete-of-insert-many-when-not-equal
  (implies (not (equal x y))
           (equal (delete x (insert-many y n bag))
                  (insert-many y n (delete x bag))))
  :enable (extensionality
           count-of-delete
           count-of-insert-many))

(defrule delete-of-insert-many-when-not-equal-cheap
  (implies (not (equal x y))
           (equal (delete x (insert-many y n bag))
                  (insert-many y n (delete x bag))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by delete-of-insert-many-when-not-equal)

(defruled delete-many-of-arg1-and-insert
  (equal (delete-many x n (insert x bag))
         (if (equal (nfix n) 0)
             (insert x bag)
           (delete-many x (- (nfix n) 1) bag)))
  :enable (extensionality
           count-of-delete-many
           count-of-insert
           nfix))

(defruled delete-many-of-insert-when-not-equal
  (implies (not (equal x y))
           (equal (delete-many x n (insert y bag))
                  (insert y (delete-many x n bag))))
  :enable (extensionality
           count-of-delete-many
           count-of-insert))

(defrule delete-many-of-insert-when-not-equal-cheap
  (implies (not (equal x y))
           (equal (delete-many x n (insert y bag))
                  (insert y (delete-many x n bag))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by delete-many-of-insert-when-not-equal)

;; Nests of deletes are sorted by element, whether a layer is delete or
;; delete-many. Where an element has both, delete comes outside.

(defrule delete-many-of-delete
  (equal (delete-many x n (delete y bag))
         (delete y (delete-many x n bag)))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :enable (extensionality
           count-of-delete-many
           count-of-delete
           nfix))

(defrule delete-of-delete-many
  (equal (delete x (delete-many y n bag))
         (delete-many y n (delete x bag)))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :enable (extensionality
           count-of-delete-many
           count-of-delete
           nfix))

(defrule delete-many-of-arg1-and-delete
  (equal (delete-many x n (delete x bag))
         (delete x (delete-many x n bag)))
  :enable (extensionality
           count-of-delete-many
           count-of-delete
           nfix))

(defruled delete-of-delete-many-becomes-delete-many
  (equal (delete x (delete-many x n bag))
         (delete-many x (+ (nfix n) 1) bag))
  :enable (extensionality
           count-of-delete-many
           count-of-delete
           nfix))

;;;;;;;;;;;;;;;;;;;;

;; The normal form for a single occurrence is delete. This must come after
;; every proof that enables delete, since the two would loop.

(defrule delete-many-of-1
  (equal (delete-many x 1 bag)
         (delete x bag))
  :enable delete)

(theory-invariant (incompatible! (:definition delete$inline)
                                 (:rewrite delete-many-of-1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy delete-extra-rules
  '(count-of-delete-many
    count-of-delete
    delete-many-when-count-0
    delete-when-count-0
    cardinality-of-delete-many
    cardinality-of-delete
    delete-many-of-arg1-and-insert-many
    delete-of-insert
    delete-of-arg1-and-insert-many
    delete-many-of-arg1-and-insert
    ))
