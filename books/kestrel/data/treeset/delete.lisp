; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
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

(include-book "internal/join-defs")
(include-book "internal/delete-defs")
(include-book "set-defs")
(include-book "cardinality-defs")
(include-book "in-defs")
(include-book "subset-defs")
(include-book "insert-defs")
(include-book "to-oset-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/osets/top" :dir :system))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))

(local (include-book "to-oset"))
(local (include-book "internal/tree"))
(local (include-book "internal/join"))
(local (include-book "internal/delete"))
(local (include-book "internal/count"))
(local (include-book "internal/in"))
(local (include-book "internal/in-order"))
(local (include-book "set"))
(local (include-book "to-oset"))
(local (include-book "cardinality"))
(local (include-book "in"))
(local (include-book "subset"))
(local (include-book "extensionality"))
(local (include-book "insert"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc delete
  :parents (treeset)
  :short "Remove a value (or multiple values) from a @(see treeset)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(n))$) (for a single delete).")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(delete x-0 x-1 ... x-n set :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the set consists of elements
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-macro-loop
  (delete
   (list true-listp))
  :guard (and (consp list)
              (consp (rest list))
              (member-eq delete
                         '(delete$inline delete-= delete-eq delete-eql)))
  (if (endp (rest (rest list)))
      (list delete
            (first list)
            (second list))
    (list delete
          (first list)
          (delete-macro-loop delete (rest list))))
  :hints (("Goal" :in-theory (enable acl2-count))))

(define delete-macro-fn
  ((list true-listp))
  (mv-let (erp rest alist)
          (partition-rest-and-keyword-args list '(:test))
    (cond (erp
           (er hard? 'delete "Arguments are ill-formed: ~x0" list))
          ((or (not (consp rest))
               (not (consp (rest rest))))
           (er hard? 'delete "Too few arguments: ~x0" list))
          (t (let ((test? (assoc-eq :test alist)))
               (if test?
                   (let ((test (cdr test?)))
                     (case test
                       (equal (delete-macro-loop 'delete$inline rest))
                       (= (delete-macro-loop 'delete-= rest))
                       (eq (delete-macro-loop 'delete-eq rest))
                       (eql (delete-macro-loop 'delete-eql rest))
                       (otherwise
                        (er hard? 'delete
                            "Keyword argument :test should have one of the ~
                             following values: equal, =, eq, or eql.~%~
                             Instead, it has value: ~x0" test))))
                 (delete-macro-loop 'delete$inline rest))))))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

(defmacro delete (&rest forms)
  (declare (xargs :guard t))
  (delete-macro-fn forms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete$inline
  (x
   (set setp))
  :returns (set$ setp
                 :hints (("Goal" :in-theory (enable setp
                                                    fix
                                                    empty))))
  (tree-delete x (fix set))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction)))

  ///
  (add-macro-fn delete delete$inline t))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t delete)))

(defruled delete-type-prescription
  (or (consp (delete x set))
      (equal (delete x set) nil))
  :rule-classes :type-prescription
  :enable delete)

(add-to-ruleset break-abstraction '(delete-type-prescription))

(defrule delete-when-set-equiv-congruence
  (implies (equiv set0 set1)
           (equal (delete x set0)
                  (delete x set1)))
  :rule-classes :congruence
  :enable delete)

(defrule in-of-delete
  (equal (in x (delete y set))
         (and (not (equal x y))
              (in x set)))
  :enable (in
           delete
           fix
           setp
           empty))

(defrule delete-commutative
  (equal (delete y x set)
         (delete x y set))
  :enable extensionality)

(defrule delete-contraction
  (equal (delete x x set)
         (delete x set))
  :enable extensionality)

(defruled delete-when-not-in
  (implies (not (in x set))
           (equal (delete x set)
                  (fix set)))
  :enable extensionality)

(defrule delete-when-not-in-cheap
  (implies (not (in x set))
           (equal (delete x set)
                  (fix set)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by delete-when-not-in)

(defrule delete-of-insert
  (equal (delete x (insert x set))
         (delete x set))
  :enable extensionality)

(defrule insert-of-delete
  (equal (insert x (delete x set))
         (insert x set))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;

(defruled cardinality-of-delete
  (equal (cardinality (delete x set))
         (if (in x set)
             (- (cardinality set) 1)
           (cardinality set)))
  :enable (cardinality
           delete
           in
           fix
           setp
           empty))

(defrule cardinality-of-delete-when-in
  (implies (in x set)
           (equal (cardinality (delete x set))
                  (- (cardinality set) 1)))
  :use cardinality-of-delete)

(defrule cardinality-of-delete-when-not-in
  (implies (not (in x set))
           (equal (cardinality (delete x set))
                  (cardinality set)))
  :use cardinality-of-delete)

;;;;;;;;;;;;;;;;;;;;

(defrule subset-of-delete
  (subset (delete x set) set)
  :enable pick-a-point)

(defrule subset-of-arg1-and-delete
  (equal (subset set (delete x set))
         (not (in x set)))
  :disable (in-when-subset-and-in
            in-when-in-and-subset)
  :use (:instance in-when-subset-and-in
                  (a x)
                  (x set)
                  (y (delete x set))))

(defrule monotonicity-of-delete
  (implies (subset set0 set1)
           (subset (delete x set0)
                   (delete x set1)))
  :enable pick-a-point)

;;;;;;;;;;;;;;;;;;;;

(defrule oset-delete-of-arg1-and-to-oset
  (equal (set::delete x (to-oset set))
         (to-oset (delete x set)))
  :enable (to-oset
           delete
           fix
           setp
           empty))

(add-to-ruleset from-oset-theory '(oset-delete-of-arg1-and-to-oset))

(defrule from-oset-of-oset-delete
  (equal (from-oset (set::delete x oset))
         (delete x (from-oset oset)))
  :enable extensionality)

(add-to-ruleset from-oset-theory '(from-oset-of-oset-delete))

(defruled oset-delete-becomes-delete
  (equal (set::delete x oset)
         (to-oset (delete x (from-oset oset))))
  :enable set::expensive-rules)

(add-to-ruleset from-oset-theory '(oset-delete-becomes-delete))

(defruled delete-becomes-oset-delete
  (equal (delete x set)
         (from-oset (set::delete x (to-oset set)))))

(add-to-ruleset to-oset-theory '(delete-becomes-oset-delete))

;;;;;;;;;;;;;;;;;;;;

(defruled oset-emptyp-of-oset-delete
  (equal (set::emptyp (set::delete x oset))
         (or (set::emptyp oset)
             (equal oset (set::insert x nil))))
  :use oset-emptyp-of-oset-delete-lemma1
  :prep-lemmas
  ((defrule oset-emptyp-of-oset-delete-lemma1
     (implies (and (not (set::emptyp oset))
                   (set::emptyp (set::delete x oset)))
              (equal oset (set::insert x nil)))
     :rule-classes nil
     :enable set::expensive-rules
     :prep-lemmas
     ((defrule oset-emptyp-of-oset-delete-lemma0
        (implies (and (set::emptyp (set::delete x oset))
                      (not (equal x y)))
                 (not (set::in y oset)))
        :use ((:instance set::delete-in
                         (acl2::a y)
                         (acl2::b x)
                         (acl2::x oset)))
        :enable set::expensive-rules
        :disable set::delete-in)))))

;; TODO: is this fine to enable by default?
(defrule emptyp-of-delete
  (equal (emptyp (delete x set))
         (or (emptyp set)
             (equal set (insert x (empty)))))
  :enable (to-oset-theory
           oset-emptyp-of-oset-delete)
  :disable from-oset-theory)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-=
  ((x acl2-numberp)
   (set acl2-number-setp))
  (mbe :logic (delete x set)
       :exec (acl2-number-tree-delete x (fix set)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            delete
                                            set-all-acl2-numberp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-eq
  ((x symbolp)
   (set symbol-setp))
  (mbe :logic (delete x set)
       :exec (symbol-tree-delete x (fix set)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            delete
                                            set-all-symbolp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-eql
  ((x eqlablep)
   (set eqlable-setp))
  (mbe :logic (delete x set)
       :exec (eqlable-tree-delete x (fix set)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            delete
                                            set-all-eqlablep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tail
  ((set setp))
  :parents (delete)
  :short "Remove the @(see head) from a nonempty @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is slightly faster than calling @(tsee delete) on the head.")
   (xdoc::p
     "Note: it is <emph>not</emph> recommended to iterate over a @(see treeset)
      using @(tsee tail) (unless you need to maintain a set of the remaining
      elements)."))
  :guard (not (emptyp set))
  (mbe :logic (delete (head set) set)
       :exec (tree-join (tree->left set)
                        (tree->right set)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            delete
                                            head
                                            tree-delete
                                            tree-join-at))))
