; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This sums the acl2-count of a list of items. It is useful as a measure for a
;; stack of work which may grow in length but shrink in the sum of its
;; items. That pattern appears often when writing fast tail-recursive functions
;; over trees. Such functions take a list of trees and often consume the head
;; of the list but cons back the left and right subtree of the head.
;; See for instance fast-tree-nodes-count in cardinality.lisp.
(define sum-acl2-count (x)
  (declare (xargs :type-prescription (natp (sum-acl2-count x))))
  (if (consp x)
      (+ (acl2-count (first x))
         (sum-acl2-count (rest x)))
    (acl2-count x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule <=-of-sum-acl2-count-and-acl2-count-linear
  (<= (sum-acl2-count x)
      (acl2-count x))
  :rule-classes :linear
  :induct t
  :enable sum-acl2-count)

(defrule <=-of-acl2-count-of-car-and-sum-acl2-count-linear
  (<= (acl2-count (car x))
      (sum-acl2-count x))
  :rule-classes :linear
  :enable (sum-acl2-count
           acl2-count))

(defrule <=-of-sum-acl2-count-of-cdr-and-sum-acl2-count-linear
  (<= (sum-acl2-count (cdr x))
      (sum-acl2-count x))
  :rule-classes :linear
  :enable (sum-acl2-count
           acl2-count))

(defrule sum-acl2-count-of-cons
  (equal (sum-acl2-count (cons x y))
         (+ (acl2-count x)
            (sum-acl2-count y)))
  :enable sum-acl2-count)
