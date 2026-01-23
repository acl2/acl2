; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)
;
; Some rules in this book are "ported" from std/osets/top.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)
(include-book "kestrel/data/utilities/list-defs" :dir :system)
(include-book "kestrel/data/utilities/oset-defs" :dir :system)

(include-book "internal/insert-defs")
(include-book "hash-defs")
(include-book "set-defs")
(include-book "to-oset-defs")
(include-book "cardinality-defs")
(include-book "in-defs")
(include-book "subset-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/fixed-size-words/u32" :dir :system))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "std/osets/top" :dir :system))
(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/bst"))
(local (include-book "internal/heap-order"))
(local (include-book "internal/heap"))
(local (include-book "internal/insert"))
(local (include-book "internal/in-order"))
(local (include-book "hash"))
(local (include-book "set"))
(local (include-book "to-oset"))
(local (include-book "cardinality"))
(local (include-book "in"))
(local (include-book "subset"))
(local (include-book "extensionality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc insert
  :parents (treeset)
  :short "Add a value (or multiples values) to a @(see treeset)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(n))$) (for a single insert).")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(insert x-0 x-1 ... x-n set :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the set consists of elements
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert-macro-loop
  (insert
   (list true-listp))
  :guard (and (consp list)
              (consp (rest list))
              (member-eq insert
                         '(insert$inline insert-= insert-eq insert-eql)))
  (if (endp (rest (rest list)))
      (list insert
            (first list)
            (second list))
    (list insert
          (first list)
          (insert-macro-loop insert (rest list))))
  :hints (("Goal" :in-theory (enable acl2-count))))

(define insert-macro-fn
  ((list true-listp))
  (mv-let (erp rest alist)
          (partition-rest-and-keyword-args list '(:test))
    (cond (erp
           (er hard? 'insert "Arguments are ill-formed: ~x0" list))
          ((not (consp rest))
           (er hard? 'insert "Too few arguments: ~x0" list))
          ((not (consp (rest rest)))
           (list 'fix (first list)))
          (t (let ((test? (assoc-eq :test alist)))
               (if test?
                   (let ((test (cdr test?)))
                     (case test
                       (equal (insert-macro-loop 'insert$inline rest))
                       (= (insert-macro-loop 'insert-= rest))
                       (eq (insert-macro-loop 'insert-eq rest))
                       (eql (insert-macro-loop 'insert-eql rest))
                       (otherwise
                        (er hard? 'insert
                            "Keyword argument :test should have one of the ~
                             following values: equal, =, eq, or eql.~%~
                             Instead, it has value: ~x0" test))))
                 (insert-macro-loop 'insert$inline rest))))))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

(defmacro insert (&rest forms)
  (declare (xargs :guard t))
  (insert-macro-fn forms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert$inline
  (x
   (set setp))
  :returns (set$ setp
                 :hints (("Goal" :in-theory (enable* break-abstraction
                                                     setp
                                                     fix))))
  (mv-let (inp set$)
          (tree-insert x (hash x) (fix set))
    (declare (ignore inp))
    set$)
  :guard-hints (("Goal" :in-theory (enable* break-abstraction)))

  ///
  (add-macro-fn insert insert$inline t))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t insert)))

(defrule insert-when-set-equiv-congruence
  (implies (equiv set0 set1)
           (equal (insert x set0)
                  (insert x set1)))
  :rule-classes :congruence
  :enable insert)

(defrule emptyp-of-insert
  (not (emptyp (insert x set)))
  :enable (emptyp
           insert
           fix
           setp))

(defruled insert-type-prescription
  (consp (insert x set))
  :rule-classes :type-prescription
  :enable emptyp
  :disable emptyp-of-insert
  :use emptyp-of-insert)

(add-to-ruleset break-abstraction '(insert-type-prescription))

(defrule in-of-insert
  (equal (in x (insert y set))
         (or (equal x y)
             (in x set)))
  :enable (in
           insert
           fix
           setp
           empty))

(defrule insert-commutative
  (equal (insert y x set)
         (insert x y set))
  :enable extensionality)

(defrule insert-contraction
  (equal (insert x x set)
         (insert x set))
  :enable extensionality)

(defruled insert-when-in
  (implies (in x set)
           (equal (insert x set)
                  (fix set)))
  :enable extensionality)

(defrule insert-when-in-cheap
  (implies (in x set)
           (equal (insert x set)
                  (fix set)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by insert-when-in)

;;;;;;;;;;;;;;;;;;;;

(defruled cardinality-of-insert
  (equal (cardinality (insert x set))
         (if (in x set)
             (cardinality set)
           (+ 1 (cardinality set))))
  :enable (cardinality
           insert
           in
           fix
           setp
           empty))

(defrule cardinality-of-insert-when-in
  (implies (in x set)
           (equal (cardinality (insert x set))
                  (cardinality set)))
  :enable cardinality-of-insert)

(defrule cardinality-of-insert-when-not-in
  (implies (not (in x set))
           (equal (cardinality (insert x set))
                  (+ 1 (cardinality set))))
  :enable cardinality-of-insert)

;;;;;;;;;;;;;;;;;;;;

(defrule subset-of-insert
  (equal (subset (insert a x) y)
         (and (subset x y)
              (in a y)))
  :enable (acl2::equal-of-booleans-cheap
           pick-a-point-polar))

(defrule subset-of-arg1-and-insert
  (subset set (insert x set))
  :enable pick-a-point)

(defrule monotonicity-of-insert
  (implies (subset x0 x1)
           (subset (insert a x0)
                   (insert a x1))))

;;;;;;;;;;;;;;;;;;;;

(defrule oset-insert-of-arg1-and-to-oset
  (equal (set::insert x (to-oset set))
         (to-oset (insert x set)))
  :enable (to-oset
           insert
           fix
           setp
           empty))

(add-to-ruleset from-oset-theory '(oset-insert-of-arg1-and-to-oset))

(defruled to-oset-of-insert
  (equal (to-oset (insert x set))
         (set::insert x (to-oset set))))

(add-to-ruleset to-oset-theory '(to-oset-of-insert))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define singleton-with-hash
  (x
   (hash (unsigned-byte-p 32 hash)))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  (mbe :logic (insert x (empty))
       :exec (tree-singleton x hash))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal
                                           insert
                                           empty))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define singleton (x)
  (mbe :logic (insert x (empty))
       :exec (tree-singleton x (hash x)))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable insert
                                           empty))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert-all
  ((list true-listp)
   (set setp))
  :returns (set$ setp)
  :parents (insert)
  :short "Add a list of values to the set."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n\\log(n+m))$), where @($n$) is the size of the list,
      and @($m$) is the size of the set."))
  (if (endp list)
      (fix set)
    (insert-all (rest list)
                (insert (first list) set))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t insert-all)))

(defruled insert-all-type-prescription
  (or (consp (insert-all list set))
      (equal (insert-all list set) nil))
  :rule-classes :type-prescription
  :induct t
  :enable (insert-all
           break-abstraction))

(add-to-ruleset break-abstraction '(insert-all-type-prescription))

(defruled insert-all-when-consp-of-arg1-type-prescription
  (implies (consp list)
           (consp (insert-all list set)))
  :rule-classes :type-prescription
  :induct t
  :enable (insert-all
           break-abstraction))

(add-to-ruleset break-abstraction
  '(insert-all-when-consp-of-arg1-type-prescription))

;;;;;;;;;;;;;;;;;;;;

(defrule insert-all-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (insert-all list set0)
                  (insert-all list set1)))
  :rule-classes :congruence
  :induct t
  :enable insert-all)

(defrule emptyp-of-insert-all
  (equal (emptyp (insert-all list set))
         (and (not (consp list))
              (emptyp set)))
  :induct t
  :enable insert-all)

(defrule in-of-insert-all
  (equal (in x (insert-all list set))
         (or (and (member-equal x list) t)
             (in x set)))
  :induct t
  :enable (insert-all
           member-equal)
  :prep-lemmas
  ((defrule in-of-insert-all-when-in
     (implies (in x set)
              (in x (insert-all list set)))
     :induct t
     :enable insert-all)))

(defrule insert-all-when-set-equiv-congruence
  (implies (set-equiv list0 list1)
           (equal (insert-all list0 set)
                  (insert-all list1 set)))
  :rule-classes :congruence
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-list
  ((list true-listp))
  :parents (treeset)
  :short "Create a set from a list of values."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is just a wrapper around @(tsee insert-all).")
   (xdoc::p
     "Time complexity: @($O(n\\log(n))$)."))
  :returns (set$ setp)
  (insert-all list (empty))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t from-list)))

(defruled from-list-type-prescription
  (or (consp (from-list list))
      (equal (from-list list) nil))
  :rule-classes :type-prescription
  :enable (from-list
           break-abstraction))

(add-to-ruleset break-abstraction '(from-list-type-prescription))

(defruled consp-of-from-list-when-consp-of-arg1-type-prescription
  (implies (consp list)
           (consp (from-list list)))
  :rule-classes :type-prescription
  :enable (from-list
           break-abstraction))

(add-to-ruleset break-abstraction
  '(consp-of-from-list-when-consp-of-arg1-type-prescription))

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-from-list
  (equal (emptyp (from-list list))
         (not (consp list)))
  :enable from-list)

(defrule in-of-from-list
  (equal (in x (from-list list))
         (and (member-equal x list) t))
  :enable from-list)

(defrule from-list-when-set-equiv-congruence
  (implies (set-equiv list0 list1)
           (equal (from-list list0)
                  (from-list list1)))
  :rule-classes :congruence
  :enable from-list
  :disable set-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc set
  :parents (treeset)
  :short "Build a @(see treeset)."
  :long
  (xdoc::topstring
    (xdoc::p
      "This is the analogue of @(tsee list) to @(see acl2::lists). It is a
       macro which constructs a chain of @(tsee insert)s.")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(set x-0 x-1 ... x-n :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the set consists of elements
           suitable for comparison with the specified equality variant.")))))

(define set-macro-fn
  ((list true-listp))
  (mv-let (erp rest alist)
          (partition-rest-and-keyword-args list '(:test))
    (cond (erp
           (er hard? 'insert "Arguments are ill-formed: ~x0" list))
          ((not (consp rest))
           '(empty))
          (t (let ((test? (assoc-eq :test alist)))
               `(insert ,@(rest list)
                        (singleton ,(first list))
                        ,@(and test? (list :test (cdr test?))))))))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

(defmacro set (&rest forms)
  (declare (xargs :guard t))
  (set-macro-fn forms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-oset ((oset set::setp))
  :parents (insert)
  :short "Build a @(see treeset) from an oset."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n\\log(n))$).")
   (xdoc::p
     "This is the inverse of @(tsee to-oset). See @(tsee to-oset) for more
      information."))
  :returns (set setp)
  (from-list (set::sfix oset)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t from-oset)))

(defruled from-oset-type-prescription
  (or (consp (from-oset oset))
      (equal (from-oset oset) nil))
  :rule-classes :type-prescription
  :enable (from-oset
           break-abstraction))

(add-to-ruleset break-abstraction '(from-oset-type-prescription))

;;;;;;;;;;;;;;;;;;;;

(defrule from-oset-of-sfix
  (equal (from-oset (sfix oset))
         (from-oset oset))
  :enable from-oset)

(defrule emptyp-of-from-oset
  (equal (emptyp (from-oset oset))
         (set::emptyp oset))
  :enable (from-oset
           set::emptyp
           sfix))

(add-to-ruleset to-oset-theory '(emptyp-of-from-oset))

(defruled oset-emptyp-becomes-emptyp
  (equal (set::emptyp oset)
         (emptyp (from-oset oset))))

(add-to-ruleset from-oset-theory '(oset-emptyp-becomes-emptyp))

(defrule in-of-from-oset
  (equal (in x (from-oset oset))
         (set::in x oset))
  :enable (from-oset
           set::in-to-member
           sfix))

(add-to-ruleset to-oset-theory '(emptyp-of-from-oset))

(defruled oset-in-becomes-in
  (equal (set::in x oset)
         (in x (from-oset oset))))

(add-to-ruleset from-oset-theory '(oset-in-becomes-in))

(defrule to-oset-of-from-oset
  (equal (to-oset (from-oset oset))
         (sfix oset))
  :enable set::expensive-rules)

(add-to-ruleset to-oset-theory '(to-oset-of-from-oset))

(defruled sfix-becomes-to-oset
  (equal (sfix oset)
         (to-oset (from-oset oset))))

(add-to-ruleset from-oset-theory '(sfix-becomes-to-oset))

(defrule cardinality-of-from-oset
  (equal (cardinality (from-oset oset))
         (set::cardinality oset))
  :disable oset-cardinality-of-to-oset
  :use (:instance oset-cardinality-of-to-oset
                  (set (from-oset oset))))

(add-to-ruleset to-oset-theory '(cardinality-of-from-oset))

(defruled oset-cardinality-becomes-cardinality
  (equal (set::cardinality oset)
         (cardinality (from-oset oset))))

(add-to-ruleset from-oset-theory '(oset-cardinality-becomes-cardinality))

(defrule from-oset-of-to-oset
  (equal (from-oset (to-oset set))
         (fix set))
  :enable extensionality)

(add-to-ruleset from-oset-theory '(from-oset-of-to-oset))

(defrule equal-of-from-oset-of-to-oset
  (equal (equal (from-oset (to-oset set)) set)
         (setp set)))

(defruled fix-becomes-from-oset
  (equal (fix set)
         (from-oset (to-oset set))))

(add-to-ruleset to-oset-theory '(fix-becomes-from-oset))

(defrule subset-of-from-oset
  (equal (subset (from-oset x) (from-oset y))
         (set::subset x y))
  :enable to-oset-theory
  :disable from-oset-theory)

(add-to-ruleset to-oset-theory '(subset-of-from-oset))

(defrule from-oset-of-oset-insert
  (equal (from-oset (set::insert x oset))
         (insert x (from-oset oset)))
  :enable extensionality)

(add-to-ruleset from-oset-theory '(from-oset-of-oset-insert))

(defruled oset-insert-becomes-insert
  (equal (set::insert x oset)
         (to-oset (insert x (from-oset oset))))
  :enable set::expensive-rules)

(add-to-ruleset from-oset-theory '(from-oset-of-oset-insert))

(defruled insert-becomes-oset-insert
  (equal (insert x set)
         (from-oset (set::insert x (to-oset set)))))

(add-to-ruleset to-oset-theory '(insert-becomes-oset-insert))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert-=
  ((x acl2-numberp)
   (set acl2-number-setp))
  (mbe :logic (insert x set)
       :exec (mv-let (inp set$)
                     (acl2-number-tree-insert x (acl2-number-hash x) (fix set))
               (declare (ignore inp))
               set$))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-acl2-numberp
                                            insert))))

(define insert-eq
  ((x symbolp)
   (set symbol-setp))
  (mbe :logic (insert x set)
       :exec (mv-let (inp set$)
                     (symbol-tree-insert x (symbol-hash x) (fix set))
               (declare (ignore inp))
               set$))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-symbolp
                                            insert))))
(define insert-eql
  ((x eqlablep)
   (set eqlable-setp))
  (mbe :logic (insert x set)
       :exec (mv-let (inp set$)
                     (eqlable-tree-insert x (eqlable-hash x) (fix set))
               (declare (ignore inp))
               set$))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-eqlablep
                                            insert))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert-with-hash
  (x
   (hash (unsigned-byte-p 32 hash))
   (set setp))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  (mbe :logic (insert x set)
       :exec (mv-let (inp set$)
                     (tree-insert x hash set)
               (declare (ignore inp))
               set$))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* data::u32-equal
                                            break-abstraction
                                            insert))))
