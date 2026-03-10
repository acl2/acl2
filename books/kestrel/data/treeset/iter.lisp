; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "internal/iter-defs")
(include-book "set-defs")
(include-book "min-max-defs")
(include-book "cardinality-defs")
(include-book "delete-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "internal/tree"))
(local (include-book "internal/iter"))
(local (include-book "set"))
(local (include-book "min-max"))
(local (include-book "cardinality"))
(local (include-book "delete"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc iterator
  :parents (treeset)
  :short "Iterators over @(see treeset)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "We cannot iterate directly over a @(see treeset) without exposing its
       underlying tree structure. To provide a convenient interface to iterate
       over @(see treeset)s abstractly, we provide @(see iterator) objects.
       @(see Iterator)s are created with @(tsee iter). Then one can iterate
       tail recursively, calling @(tsee value) to get the current element, and
       @(tsee next) to advance the iterator, unless it is @(tsee donep).
       Such a recursive function obviously terminates under
       @(tsee iter-measure).")
    (xdoc::p
      "An @(see iterator) walks over a @(see treeset) <i>in order</i>. That is,
       the @(tsee value) of an @(see iterator) is the @(tsee min) of the
       corresponding @(see treeset) (which can be constructed with
       @(tsee from-iter)), and the @(see treeset) of an @(see iterator) after
       calling @(tsee next) is the result of deleting the @(tsee min).")
    (xdoc::p
      "The process of creating and advancing all the way through an iterator
       takes @($O(n)$) time, although an individual operation may take
       @($O(\\log(n))$) time.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iterp ((x))
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  :parents (iterator)
  :short "Recognizer for @(see iterator)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "This function is intended for logical use. It should probably not be
      called in programs due to its time complexity (something like
      @($O(n\\log^2(n))$))."))
  (and (tree-iter-p x)
       (all-well-formed-p x)
       (pairwise-tree-subset-p-of-left x)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t iterp)))

(defruled iterp-compound-recognizer
  (if (iterp x)
      (true-listp x)
    (not (equal x nil)))
  :rule-classes :compound-recognizer
  :enable iterp)

(add-to-ruleset break-abstraction '(iterp-compound-recognizer))

(defruled tree-iter-p-when-iterp-forward-chaining
  (implies (iterp iter)
           (tree-iter-p iter))
  :rule-classes :forward-chaining
  :enable iterp)

(add-to-ruleset break-abstraction
                '(tree-iter-p-when-iterp-forward-chaining))

(defruled all-well-formed-p-when-iterp-forward-chaining
  (implies (iterp iter)
           (all-well-formed-p iter))
  :rule-classes :forward-chaining
  :enable iterp)

(add-to-ruleset break-abstraction
                '(all-well-formed-p-when-iterp-forward-chaining))

(defruled pairwise-tree-subset-p-of-left-when-iterp-forward-chaining
  (implies (iterp iter)
           (pairwise-tree-subset-p-of-left iter))
  :rule-classes :forward-chaining
  :enable iterp)

(add-to-ruleset break-abstraction
                '(pairwise-tree-subset-p-of-left-when-iterp-forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter ((set setp))
  :returns (iter iterp
                 :hints (("Goal" :in-theory (enable* iterp
                                                     break-abstraction))))
  :parents (iterator)
  :short "Construct an iterator from a @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(\\log(n))$)."))
  (tree-left-spine (fix set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:e iter) (:t iter)))

(defrule iter-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (iter set0)
                  (iter set1)))
  :rule-classes :congruence
  :enable iter)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter-fix ((iter iterp))
  :returns (iter$ iterp)
  :parents (iterator)
  :short "Fixer for @(see iterator)s."
  (mbe :logic (if (iterp iter)
                  iter
                (iter (empty)))
       :exec iter))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:e iter-fix) (:t iter-fix)))

(defrule iter-fix-when-iterp
  (implies (iterp iter)
           (equal (iter-fix iter)
                  iter))
  :enable iter-fix)

(defruled iter-fix-when-not-iterp
  (implies (not (iterp iter))
           (equal (iter-fix iter)
                  (iter (empty))))
  :enable iter-fix)

(defrule iter-fix-when-not-iterp-cheap
  (implies (not (iterp iter))
           (equal (iter-fix iter)
                  (iter (empty))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by iter-fix-when-not-iterp)

(defruled tree-iter-p-of-iter-fix
  (tree-iter-p (iter-fix iter))
  :enable (iter-fix
           empty
           iter
           break-abstraction))

(add-to-ruleset break-abstraction '(tree-iter-p-of-iter-fix))

(defruled all-well-formed-p-of-iter-fix
  (all-well-formed-p (iter-fix iter))
  :enable (iter-fix
           empty
           iter
           break-abstraction))

(add-to-ruleset break-abstraction '(all-well-formed-p-of-iter-fix))

(defruled pairwise-tree-subset-p-of-left-of-iter-fix
  (pairwise-tree-subset-p-of-left (iter-fix iter))
  :enable (iter-fix
           empty
           iter
           break-abstraction))

(add-to-ruleset break-abstraction
                '(pairwise-tree-subset-p-of-left-of-iter-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter-equiv
  ((x iterp)
   (y iterp))
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  :parents (iterator)
  :short "Equivalence up to @(tsee iter-fix)."
  (equal (iter-fix x)
         (iter-fix y))
  :inline t

  ///

  (defequiv iter-equiv))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t iter-equiv)))

(defrule iter-fix-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (iter-fix iter0)
                  (iter-fix iter1)))
  :rule-classes :congruence
  :enable iter-equiv)

(defrule iter-fix-under-iter-equiv
  (iter-equiv (iter-fix iter)
              iter)
  :enable iter-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter-empty ()
  :returns (empty iterp)
  :parents (iterator)
  :short "Construct an empty @(see iterator)."
  :long
  (xdoc::topstring
   (xdoc::p
     "We leave this definition enabled, reasoning directly about
      @('(iter (empty))'). It is provided as an efficient alternative to this
      logical form."))
  (mbe :logic (iter (empty))
       :exec nil)
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable iter empty))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:e iter-empty) (:t iter-empty)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define donep ((iter iterp))
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  :parents (iterator)
  :short "Check whether an @(see iterator) is done."
  :long
  (xdoc::topstring
   (xdoc::p
     "An iterator is done if the corresponding @(see treeset) is
      @(see empty)."))
  (mbe :logic (equal (iter-fix iter) (iter (empty)))
       :exec (endp iter))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* iter
                                            empty
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t donep)))

(defrule donep-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (donep iter0)
                  (donep iter1)))
  :rule-classes :congruence
  :enable donep)

(defrule donep-of-iter-empty
  (donep (iter (empty)))
  :enable donep)

(defrule iter-under-iter-equiv-whe-donep
  (implies (donep iter)
           (iter-equiv iter
                       (iter (empty))))
  :rule-classes nil
  :enable donep)

(defrule iter-under-iter-equiv-whe-donep-forward-chaining
  (implies (donep iter)
           (iter-equiv iter
                       (iter (empty))))
  :rule-classes :forward-chaining
  :by iter-under-iter-equiv-whe-donep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-iter ((iter iterp))
  :returns (set setp
                :hints (("Goal" :in-theory (enable* setp
                                                    break-abstraction))))
  :parents (iterator)
  :short "Construct a @(see treeset) from an @(see iterator)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Iterators are mainly characterized by the @(see treeset)s they map to
      under this function.")
   (xdoc::p
     "The time complexity is @($O(n)$). This is not optimal &mdash; it could be
      done in @($O(\\log(n))$) time. (See @(tsee tree-iter-to-tree) for
      implementation details.)"))
  (tree-iter-to-tree (iter-fix iter))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t from-iter)))

(defrule from-iter-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (from-iter iter0)
                  (from-iter iter1)))
  :rule-classes :congruence
  :enable from-iter)

(defrule emptyp-of-from-iter
  (equal (emptyp (from-iter iter))
         (donep iter))
  :enable (from-iter
           emptyp
           iter-fix
           donep
           empty
           iter
           setp
           break-abstraction))

(defrule from-iter-of-iter
  (equal (from-iter (iter set))
         (fix set))
  :enable (iter
           from-iter
           iter-fix
           fix
           setp
           empty
           iterp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value ((iter iterp))
  :guard (not (donep iter))
  :parents (iterator)
  :short "Get the current element from an @(see iterator)."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is the @(tsee min) of @('(from-iter iter)'). When the iterator is
      @(tsee donep), the logical result is @('nil'). The time complexity is
      @($O(1)$)."))
  (mbe :logic (min (from-iter iter))
       :exec (tree-iter-value iter))
  :guard-hints (("Goal" :in-theory (enable* iter
                                            empty
                                            from-iter
                                            min
                                            setp
                                            tree-iter-value-becomes-tree-min
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule value-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (value iter0)
                  (value iter1)))
  :rule-classes :congruence
  :enable value)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define next ((iter iterp))
  :guard (not (donep iter))
  :returns (iter$ iterp
                  :hints (("Goal" :in-theory (enable* iterp
                                                      break-abstraction))))
  :parents (iterator)
  :short "Advance the @(see iterator)."
  :long
  (xdoc::topstring
   (xdoc::p
     "The time complexity of advancing through the entire iterator is
      @($O(n)$). Thus, the amortized cost of @(tsee next) is @($O(1)$),
      although the worst case for a single call is @($O(\\log(n))$)."))
  (tree-iter-next (iter-fix iter))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule next-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (next iter0)
                  (next iter1)))
  :rule-classes :congruence
  :enable next)

(defruled next-when-donep
  (implies (donep iter)
           (equal (next iter)
                  (iter (empty))))
  :enable (next
           donep
           empty
           iter))

(defrule next-when-donep-cheap
  (implies (donep iter)
           (equal (next iter)
                  (iter (empty))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by next-when-donep)

(defrule next-of-iter-empty
  (equal (next (iter (empty)))
         (iter (empty)))
  :enable next-when-donep)

(defrule from-iter-of-next
  (equal (from-iter (next iter))
         (delete (min (from-iter iter))
                 (from-iter iter)))
  :enable (from-iter
           next
           min
           delete
           iterp
           iter
           setp
           tree-iter-value-becomes-tree-min
           break-abstraction))

;; TODO: prove it first about tree-iter-next
;; - Also, we'll want variations for equal of iter-fix, and iter-equiv
;; (defrule equal-of-next-arg1-and-arg1
;;   (equal (equal (next iter) iter)
;;          (equal iter (iter (empty))))
;;   :enable ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter-measure ((iter iterp))
  :returns (measure natp :rule-classes (:rewrite :type-prescription))
  :parents (iterator)
  :short "A suitable measure for @(see iterator)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "This measure decreases on @(tsee next), if the @(see iterator) is not
      @(tsee donep)."))
  (cardinality (from-iter iter)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t iter-measure)))

(defrule iter-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (iter-measure iter0)
                  (iter-measure iter1)))
  :rule-classes :congruence
  :enable iter-measure)

(defrule iter-measure-when-donep
  (implies (donep iter)
           (equal (iter-measure iter)
                  0))
  :enable iter-measure)

(defruled iter-measure-of-next
  (equal (iter-measure (next iter))
         (if (donep iter)
             0
           (- (iter-measure iter) 1)))
  :enable iter-measure)

(defrule iter-measure-of-next-when-not-donep-cheap
  (implies (not (donep iter))
           (equal (iter-measure (next iter))
                  (- (iter-measure iter) 1)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :use iter-measure-of-next)

(defrule iter-measure-of-next-linear
  (<= (iter-measure (next iter))
      (iter-measure iter))
  :rule-classes :linear
  :enable iter-measure-of-next)

(defrule iter-measure-of-next-linear-when-not-donep
  (implies (not (donep iter))
           (< (iter-measure (next iter))
              (iter-measure iter)))
  :rule-classes :linear
  :enable iter-measure-of-next)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: typed/equal-variants ?
