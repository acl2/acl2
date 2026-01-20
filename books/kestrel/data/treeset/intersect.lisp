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

(include-book "kestrel/data/utilities/oset-defs" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/intersect-defs")
(include-book "set-defs")
(include-book "cardinality-defs")
(include-book "subset-defs")
(include-book "insert-defs")
(include-book "delete-defs")
(include-book "union-defs")
(include-book "to-oset-defs")
(include-book "generic-typed-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/osets/top" :dir :system))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/intersect"))
(local (include-book "internal/in"))
(local (include-book "internal/in-order"))
(local (include-book "to-oset"))
(local (include-book "set"))
(local (include-book "in"))
(local (include-book "cardinality"))
(local (include-book "subset"))
(local (include-book "extensionality"))
(local (include-book "insert"))
(local (include-book "delete"))
(local (include-book "union"))
(local (include-book "generic-typed"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc intersect
  :parents (treeset)
  :short "An @($n$)-ary set intersection on @(see treeset)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(m\\log(n/m))$) (for binary intersection, where
       @($m < n$)).")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(intersect set-0 set-1 ... set-n :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the set consists of elements
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define intersect-macro-loop
  (intersect
   (list true-listp))
  :guard (and (consp list)
              (consp (rest list))
              (member-eq intersect
                         '(intersect$inline intersect-= intersect-eq
                           intersect-eql)))
  (if (endp (rest (rest list)))
      (list intersect
            (first list)
            (second list))
    (list intersect
          (first list)
          (intersect-macro-loop intersect (rest list))))
  :hints (("Goal" :in-theory (enable acl2-count))))

(define intersect-macro-fn
  ((list true-listp))
  (mv-let (erp rest alist)
          (partition-rest-and-keyword-args list '(:test))
    (cond (erp
           (er hard? 'intersect "Arguments are ill-formed: ~x0" list))
          ((or (not (consp rest))
               (not (consp (rest rest))))
           (er hard? 'intersect "Too few arguments: ~x0" list))
          (t (let ((test? (assoc-eq :test alist)))
               (if test?
                   (let ((test (cdr test?)))
                     (case test
                       (equal (intersect-macro-loop 'intersect$inline rest))
                       (=     (intersect-macro-loop 'intersect-=      rest))
                       (eq    (intersect-macro-loop 'intersect-eq     rest))
                       (eql   (intersect-macro-loop 'intersect-eql    rest))
                       (otherwise
                        (er hard? 'intersect
                            "Keyword argument :test should have one of the ~
                             following values: equal, =, eq, or eql.~%~
                             Instead, it has value: ~x0" test))))
                 (intersect-macro-loop 'intersect$inline rest))))))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

(defmacro intersect (&rest forms)
  (declare (xargs :guard t))
  (intersect-macro-fn forms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define intersect$inline
  ((x setp)
   (y setp))
  :returns (set setp
                :hints (("Goal" :in-theory (enable setp
                                                   fix
                                                   empty))))
  (tree-intersect (fix x) (fix y))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction)))

  ///
  (add-macro-fn intersect intersect$inline t))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t intersect)))

(defruled intersect-type-prescription
  (or (consp (intersect x y))
      (equal (intersect x y) nil))
  :rule-classes :type-prescription
  :enable intersect)

(add-to-ruleset break-abstraction '(intersect-type-prescription))

(defrule intersect-when-set-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (intersect x0 z)
                  (intersect x1 z)))
  :rule-classes :congruence
  :enable intersect)

(defrule intersect-when-set-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (intersect x y0)
                  (intersect x y1)))
  :rule-classes :congruence
  :enable intersect)

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-intersect-when-emptyp-of-arg1
  (implies (emptyp x)
           (emptyp (intersect x y)))
  :enable (emptyp
           intersect
           fix
           empty))

(defrule emptyp-of-intersect-when-emptyp-of-arg2
  (implies (emptyp y)
           (emptyp (intersect x y)))
  :enable (emptyp
           intersect
           fix
           empty))

(defrule in-of-intersect
  (equal (in a (intersect x y))
         (and (in a x)
              (in a y)))
  :enable (intersect
           in
           fix
           empty
           setp))

;;;;;;;;;;;;;;;;;;;;

(defrule subset-of-intersect0
  (subset (intersect x y) x)
  :enable pick-a-point)

(defrule subset-of-intersect1
  (subset (intersect x y) y)
  :enable pick-a-point)

(defrule subset-of-arg1-and-intersect0
  (equal (subset x (intersect x y))
         (subset x y))
  :enable (acl2::equal-of-booleans-cheap
           pick-a-point-polar))

(defrule subset-of-arg1-and-intersect1
  (equal (subset x (intersect y x))
         (subset x y))
  :enable (acl2::equal-of-booleans-cheap
           pick-a-point-polar))

(defrule monotonicity-of-intersect
  (implies (and (subset x0 x1)
                (subset y0 y1))
           (subset (intersect x0 y0)
                   (intersect x1 y1)))
  :enable pick-a-point)

;;;;;;;;;;;;;;;;;;;;

(defrule associativity-of-intersect
  (equal (intersect (intersect x y) z)
         (intersect x y z))
  :enable extensionality)

(defrule commutativity-of-intersect
  (equal (intersect y x)
         (intersect x y))
  :enable extensionality)

(defrule idempotence-of-intersect
  (equal (intersect x x)
         (fix x))
  :enable extensionality)

(defrule intersect-contraction
  (equal (intersect x x y)
         (intersect x y))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;

(defruled intersect-when-emptyp-of-arg1
  (implies (emptyp x)
           (equal (intersect x y)
                  (empty)))
  :enable extensionality)

(defrule intersect-when-emptyp-of-arg1-cheap
  (implies (emptyp x)
           (equal (intersect x y)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by intersect-when-emptyp-of-arg1)

(defrule intersect-of-empty
  (equal (intersect (empty) y)
         (empty))
  :enable intersect-when-emptyp-of-arg1)

(defruled intersect-when-emptyp-of-arg2
  (implies (emptyp y)
           (equal (intersect x y)
                  (empty)))
  :enable extensionality)

(defrule intersect-when-emptyp-of-arg2-cheap
  (implies (emptyp y)
           (equal (intersect x y)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by intersect-when-emptyp-of-arg2)

(defrule intersect-of-arg1-and-empty
  (equal (intersect x (empty))
         (empty))
  :enable intersect-when-emptyp-of-arg2)

(defruled intersect-of-insert
  (equal (intersect (insert a x) y)
         (if (in a y)
             (insert a (intersect x y))
           (intersect x y)))
  :enable extensionality)

(defruled intersect-of-insert-when-in-of-arg2
  (implies (in a y)
           (equal (intersect (insert a x) y)
                  (insert a (intersect x y))))
  :by intersect-of-insert)

(defrule intersect-of-insert-when-in-of-arg2-cheap
  (implies (in a y)
           (equal (intersect (insert a x) y)
                  (insert a (intersect x y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by intersect-of-insert-when-in-of-arg2)

(defruled intersect-of-insert-when-not-in-of-arg2
  (implies (not (in a y))
           (equal (intersect (insert a x) y)
                  (intersect x y)))
  :by intersect-of-insert)

(defrule intersect-of-insert-when-not-in-of-arg2-cheap
  (implies (not (in a y))
           (equal (intersect (insert a x) y)
                  (intersect x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by intersect-of-insert-when-not-in-of-arg2)

(defruled intersect-of-arg1-and-insert
  (equal (intersect x (insert a y))
         (if (in a x)
             (insert a (intersect x y))
           (intersect x y)))
  :enable extensionality)

(defruled intersect-of-arg1-and-insert-when-in-of-arg1
  (implies (in a x)
           (equal (intersect x (insert a y))
                  (insert a (intersect x y))))
  :by intersect-of-arg1-and-insert)

(defrule intersect-of-arg1-and-insert-when-in-of-arg1-cheap
  (implies (in a x)
           (equal (intersect x (insert a y))
                  (insert a (intersect x y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by intersect-of-arg1-and-insert-when-in-of-arg1)

(defruled intersect-of-arg1-and-insert-when-not-in-of-arg1
  (implies (not (in a x))
           (equal (intersect x (insert a y))
                  (intersect x y)))
  :by intersect-of-arg1-and-insert)

(defrule intersect-of-arg1-and-insert-when-not-in-of-arg1-cheap
  (implies (not (in a x))
           (equal (intersect x (insert a y))
                  (intersect x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by intersect-of-arg1-and-insert-when-not-in-of-arg1)

(defrule intersect-of-delete
  (equal (intersect (delete a x) y)
         (delete a (intersect x y)))
  :enable extensionality)

(defrule intersect-of-arg1-and-delete
  (equal (intersect x (delete a y))
         (delete a (intersect x y)))
  :enable extensionality)

(defruled union-over-intersect
  (equal (union (intersect x y) z)
         (intersect (union x z) (union y z)))
  :enable extensionality)

(defruled union-over-arg1-intersect
  (equal (union x (intersect y z))
         (intersect (union x y) (union x z)))
  :enable extensionality)

(defrule intersect-over-union
  (equal (intersect (union x y) z)
         (union (intersect x z) (intersect y z)))
  :enable extensionality)

(defrule intersect-over-arg1-and-union
  (equal (intersect x (union y z))
         (union (intersect x y) (intersect x z)))
  :enable extensionality)

(defruled intersect-when-subset-arg1-arg2
  (implies (subset x y)
           (equal (intersect x y)
                  (fix x)))
  :enable extensionality)

(defrule intersect-when-subset-arg1-arg2-cheap
  (implies (subset x y)
           (equal (intersect x y)
                  (fix x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by intersect-when-subset-arg1-arg2)

(defruled intersect-when-subset-arg2-arg1
  (implies (subset y x)
           (equal (intersect x y)
                  (fix y)))
  :enable extensionality)

(defrule intersect-when-subset-arg2-arg1-cheap
  (implies (subset y x)
           (equal (intersect x y)
                  (fix y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by intersect-when-subset-arg2-arg1)

;;;;;;;;;;;;;;;;;;;;

(defrule set-all-genericp-of-intersect-when-set-all-genericp-of-arg1
  (implies (set-all-genericp x)
           (set-all-genericp (intersect x y)))
  :enable set-all-genericp-pick-a-point-polar)

(defrule set-all-genericp-of-intersect-when-set-all-genericp-of-arg2
  (implies (set-all-genericp y)
           (set-all-genericp (intersect x y)))
  :enable set-all-genericp-pick-a-point-polar)

(defrule set-all-acl2-numberp-of-intersect-when-set-all-acl2-numberp-of-arg1
  (implies (set-all-acl2-numberp x)
           (set-all-acl2-numberp (intersect x y)))
  :use (:functional-instance
         set-all-genericp-of-intersect-when-set-all-genericp-of-arg1
         (genericp acl2-numberp)
         (set-all-genericp set-all-acl2-numberp))
  :enable set-all-acl2-numberp-alt-definition)

(defrule set-all-acl2-numberp-of-intersect-when-set-all-acl2-numberp-of-arg2
  (implies (set-all-acl2-numberp y)
           (set-all-acl2-numberp (intersect x y)))
  :use (:functional-instance
         set-all-genericp-of-intersect-when-set-all-genericp-of-arg2
         (genericp acl2-numberp)
         (set-all-genericp set-all-acl2-numberp)))

(defrule set-all-symbolp-of-intersect-when-set-all-symbolp-of-arg1
  (implies (set-all-symbolp x)
           (set-all-symbolp (intersect x y)))
  :use (:functional-instance
         set-all-genericp-of-intersect-when-set-all-genericp-of-arg1
         (genericp symbolp)
         (set-all-genericp set-all-symbolp))
  :enable set-all-symbolp-alt-definition)

(defrule set-all-symbolp-of-intersect-when-set-all-symbolp-of-arg2
  (implies (set-all-symbolp y)
           (set-all-symbolp (intersect x y)))
  :use (:functional-instance
         set-all-genericp-of-intersect-when-set-all-genericp-of-arg2
         (genericp symbolp)
         (set-all-genericp set-all-symbolp)))

(defrule set-all-eqlablep-of-intersect-when-set-all-eqlablep-of-arg1
  (implies (set-all-eqlablep x)
           (set-all-eqlablep (intersect x y)))
  :use (:functional-instance
         set-all-genericp-of-intersect-when-set-all-genericp-of-arg1
         (genericp eqlablep)
         (set-all-genericp set-all-eqlablep))
  :enable set-all-eqlablep-alt-definition)

(defrule set-all-eqlablep-of-intersect-when-set-all-eqlablep-of-arg2
  (implies (set-all-eqlablep y)
           (set-all-eqlablep (intersect x y)))
  :use (:functional-instance
         set-all-genericp-of-intersect-when-set-all-genericp-of-arg2
         (genericp eqlablep)
         (set-all-genericp set-all-eqlablep)))

;;;;;;;;;;;;;;;;;;;;

(defrule oset-intersect-of-to-oset
  (equal (set::intersect (to-oset x)
                         (to-oset y))
         (to-oset (intersect x y)))
  :enable (to-oset
           intersect
           fix
           setp
           empty))

(add-to-ruleset from-oset-theory '(oset-intersect-of-to-oset))

(defrule from-oset-of-oset-intersect
  (equal (from-oset (set::intersect x y))
         (intersect (from-oset x)
                    (from-oset y)))
  :enable extensionality)

(add-to-ruleset from-oset-theory '(from-oset-of-oset-intersect))

(defruled oset-intersect-becomes-intersect
  (equal (set::intersect x y)
         (to-oset (intersect (from-oset x)
                             (from-oset y))))
  :enable set::expensive-rules)

(add-to-ruleset from-oset-theory '(oset-intersect-becomes-intersect))

(defruled intersect-becomes-oset-intersect
  (equal (intersect x y)
         (from-oset (set::intersect (to-oset x)
                                    (to-oset y)))))

(add-to-ruleset to-oset-theory '(intersect-becomes-oset-intersect))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule cardinality-of-intersect0-linear
  (<= (cardinality (intersect x y))
      (cardinality x))
  :rule-classes :linear
  :enable to-oset-theory
  :disable from-oset-theory)

(defrule cardinality-of-intersect1-linear
  (<= (cardinality (intersect x y))
      (cardinality y))
  :rule-classes :linear
  :enable to-oset-theory
  :disable from-oset-theory)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define intersect-=
  ((x acl2-number-setp)
   (y acl2-number-setp))
  (mbe :logic (intersect x y)
       :exec (acl2-number-tree-intersect x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-acl2-numberp
                                            intersect))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define intersect-eq
  ((x symbol-setp)
   (y symbol-setp))
  (mbe :logic (intersect x y)
       :exec (symbol-tree-intersect x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-symbolp
                                            intersect))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define intersect-eql
  ((x eqlable-setp)
   (y eqlable-setp))
  (mbe :logic (intersect x y)
       :exec (eqlable-tree-intersect x y))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-eqlablep
                                            intersect))))
