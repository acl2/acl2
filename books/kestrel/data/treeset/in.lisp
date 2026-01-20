; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/utilities/oset-defs" :dir :system)
(include-book "kestrel/utilities/polarity" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/in-defs")
(include-book "set-defs")
(include-book "to-oset-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/osets/top" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/in"))
(local (include-book "internal/in-order"))
(local (include-book "set"))
(local (include-book "to-oset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc in
  :parents (treeset)
  :short "Determine if a value is a member of a @(see treeset)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(log(n))$).")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(in x set :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that the set consists of elements
           suitable for comparison with the specified equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro in (x set &key (test 'equal))
  (declare (xargs :guard (member-eq test '(equal = eq eql))))
  (case test
    (equal `(in$inline ,x ,set))
    (=     `(in-=      ,x ,set))
    (eq    `(in-eq     ,x ,set))
    (eql   `(in-eql    ,x ,set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in$inline
  (x
   (set setp))
  :returns (yes/no booleanp)
  (mbe :logic (tree-in x (fix set))
       :exec (tree-search-in x set))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction)))

  ///
  (add-macro-fn in in$inline))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t in)))

(defrule in-type-prescription
  (booleanp (in x set))
  :rule-classes ((:type-prescription :typed-term (in x set))))

(defrule in-when-set-equiv-congruence
  (implies (equiv set0 set1)
           (equal (in x set0)
                  (in x set1)))
  :rule-classes :congruence
  :enable in)

(defruled in-when-emptyp
  (implies (emptyp set)
           (not (in x set)))
  :enable (in
           emptyp))

(defrule in-when-emptyp-cheap
  (implies (emptyp set)
           (not (in x set)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable in-when-emptyp)

(defrule in-of-arg1-and-empty
  (not (in x (empty)))
  :enable in-when-emptyp)

(defrule in-of-head
  (equal (in (head set) set)
         (not (emptyp set)))
  :enable (in
           head
           emptyp))

;;;;;;;;;;;;;;;;;;;;

(defrule oset-in-of-to-oset
  (equal (set::in x (to-oset set))
         (in x set))
  :enable (to-oset
           in
           fix
           setp
           empty))

(add-to-ruleset from-oset-theory '(oset-in-of-to-oset))

(defruled in-becomes-oset-in
  (equal (in x set)
         (set::in x (to-oset set))))

(add-to-ruleset to-oset-theory '(in-becomes-oset-in))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in-=
  ((x acl2-numberp)
   (set acl2-number-setp))
  (mbe :logic (in x set)
       :exec (acl2-number-tree-search-in x set))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-acl2-numberp
                                            in))))

(define in-eq
  ((x symbolp)
   (set symbol-setp))
  (mbe :logic (in x set)
       :exec (symbol-tree-search-in x set))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-symbolp
                                            in))))

(define in-eql
  ((x eqlablep)
   (set eqlable-setp))
  (mbe :logic (in x set)
       :exec (eqlable-tree-search-in x set))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction
                                            set-all-eqlablep
                                            in))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy in-extra-rules
  '(in-when-emptyp))
