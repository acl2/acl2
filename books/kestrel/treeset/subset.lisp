; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "in-defs")
(include-book "set-defs")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "binary-tree"))
(local (include-book "in"))
(local (include-book "set"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subset
  ((x setp)
   (y setp))
  (declare (xargs :type-prescription (booleanp (subset x y))))
  :parents (set)
  :short "Check if one set is a subset of the other."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n\\log(m))$) (Note: the current implementation is
      inefficient. This should eventually be @($O(n\\log(m/n))$), where
      @($n < m$). This may be implemented similar to @(tsee diff).)"))
  (or (emptyp x)
      (and (in (head x) y)
           (subset (left x) y)
           (subset (right x) y)))
  :hints (("Goal" :in-theory (enable o< o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule subset-when-emptyp-of-arg1
  (implies (emptyp x)
           (subset x y))
  :enable subset)

(defrule subset-when-emptyp-of-arg2
  (implies (emptyp y)
           (equal (subset x y)
                  (emptyp x)))
  :enable subset)

;; TODO: disable by default?
(defrule in-when-in-and-subset
  ;; (implies (and (in a y)
  ;;               (subset y x))
  (implies (and (subset y x)
                (in a y))
           (in a x))
  :induct t
  :enable (subset
           in
           head
           left
           right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled subset-when-subset-of-arg1-and-left
  (implies (subset x (left y))
           (subset x y))
  :induct t
  :enable subset)

(defrule subset-when-subset-of-arg1-and-left-forward-chaining
  (implies (subset x (left y))
           (subset x y))
  :rule-classes :forward-chaining
  :enable subset-when-subset-of-arg1-and-left)

(defruled subset-when-subset-of-arg1-and-right
  (implies (subset x (right y))
           (subset x y))
  :induct t
  :enable subset)

(defrule subset-when-subset-of-arg1-and-right-forward-chaining
  (implies (subset x (right y))
           (subset x y))
  :rule-classes :forward-chaining
  :enable subset-when-subset-of-arg1-and-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled subset-of-left-when-when-subset
  (implies (subset x y)
           (subset (left x) y))
  :enable subset)

(defrule subset-of-left-when-when-subset-cheap
  (implies (subset x y)
           (subset (left x) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable subset-of-left-when-when-subset)

(defruled subset-of-right-when-when-subset
  (implies (subset x y)
           (subset (right x) y))
  :enable subset)

(defrule subset-of-right-when-when-subset-cheap
  (implies (subset x y)
           (subset (right x) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable subset-of-right-when-when-subset)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()
  (defrulel subset-of-left-subset-of-right
    (and (subset (left x) x)
         (subset (right x) x))
    :induct (set-induct x)
    :enable (subset
             in-when-in-of-left
             in-when-in-of-right))

  (defrule subset-of-left
    (subset (left x) x))

  (defrule subset-of-right
    (subset (right x) x)))

(defrule subset-reflexivity
  (subset x x)
  :enable subset)

;; Note: antisymmetry is proved in double-containment.lisp

(defrule subset-transitivity
  (implies (and (subset x y)
                (subset y z))
           (subset x z))
  :induct t
  :enable subset)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled subset-when-not-in-of-head
  (implies (and (not (emptyp x))
                (not (in (head x) y)))
           (not (subset x y)))
  :disable in-when-in-and-subset
  :use ((:instance in-when-in-and-subset
                   (a (head x))
                   (x y)
                   (y x))))

(defrule subset-when-not-in-of-head-cheap
  (implies (and (not (in (head x) y))
                (not (emptyp x)))
           (not (subset x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :enable subset-when-not-in-of-head)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy subset-extra-rules
  '(subset-when-subset-of-arg1-and-left
    subset-when-subset-of-arg1-and-right
    subset-of-left-when-when-subset
    subset-of-right-when-when-subset
    subset-when-not-in-of-head))
