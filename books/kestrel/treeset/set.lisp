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

(include-book "binary-tree-defs")
(include-book "bst-defs")
(include-book "heap-defs")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "binary-tree"))
(local (include-book "bst"))
(local (include-book "heap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define setp (x)
  (declare (xargs :type-prescription (booleanp (setp x))))
  :parents (set)
  :short "Recognizer for @(see set)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n^2)$) (Note: the current implementation is
      inefficient. This should eventually be @($O(n)$) once we introduce a more
      efficient binary search tree property check via an @(tsee mbe).)"))
  (and (binary-tree-p x)
       (bst-p x)
       (heapp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule setp-compound-recognizer
  (if (setp set)
      (or (consp set)
          (equal set nil))
    (not (equal set nil)))
  :rule-classes :compound-recognizer
  :enable setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule binary-tree-p-when-setp-forward-chaining
  (implies (setp set)
           (binary-tree-p set))
  :rule-classes :forward-chaining
  :enable setp)

(defrule bst-p-when-setp-forward-chaining
  (implies (setp set)
           (bst-p set))
  :rule-classes :forward-chaining
  :enable setp)

(defrule heapp-when-setp-forward-chaining
  (implies (setp set)
           (heapp set))
  :rule-classes :forward-chaining
  :enable setp)

(defrule setp-of-tree-left-when-setp
  (implies (setp set)
           (setp (tree-left set)))
  :enable setp)

(defrule setp-of-tree-right-when-setp
  (implies (setp set)
           (setp (tree-right set)))
  :enable setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sfix ((set setp))
  :returns (set$ setp)
  :parents (set)
  :short "Fixer for @(see set)s."
  (mbe :logic (if (setp set) set nil)
       :exec (the (or cons null) set)))

(defrule sfix-when-setp
  (implies (setp set)
           (equal (sfix set)
                  set))
  :enable sfix)

(defruled sfix-when-not-setp
  (implies (not (setp set))
           (equal (sfix set)
                  nil))
  :enable sfix)

(defrule sfix-when-not-setp-cheap
  (implies (not (setp set))
           (equal (sfix set)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable sfix-when-not-setp)

(defrule sfix-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (sfix x)
                  (sfix y)))
  :rule-classes :congruence
  :enable (tree-equiv
           sfix
           setp))

(defrule bst-p-of-sfix
  (bst-p (sfix set))
  :enable sfix)

(defrule heapp-of-sfix
  (heapp (sfix set))
  :enable sfix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: rename to "equiv"? (set is implied by the package)
(define set-equiv
  ((x setp)
   (y setp))
  (declare (xargs :type-prescription (booleanp (set-equiv x y))))
  :parents (set)
  :short "Equivalence up to @(tsee sfix)."
  (equal (sfix x)
         (sfix y))
  :inline t
  :no-function t

  ///
  (defequiv set-equiv))

(defrule sfix-under-set-equiv
  (set-equiv (sfix set)
             set)
  :enable (set-equiv
           sfix))

(defrule tree-fix-under-set-equiv
  (set-equiv (tree-fix set)
             set)
  :enable set-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define emptyp ((set setp))
  (declare (xargs :type-prescription (booleanp (emptyp set))))
  :parents (set)
  :short "Check if a @(see set) is empty."
  (tree-emptyp (sfix set))
  :no-function t
  :inline t)

(defrule emptyp-when-set-equiv
  (implies (set-equiv x y)
           (equal (emptyp x)
                  (emptyp y)))
  :rule-classes :congruence
  :enable (emptyp
           set-equiv))

(defruled sfix-when-emptyp
  (implies (emptyp set)
           (equal (sfix set)
                  nil))
  :enable (emptyp
           sfix
           tree-emptyp))

(defrule sfix-when-emptyp-cheap
  (implies (emptyp set)
           (equal (sfix set)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable sfix-when-emptyp)

(defrule setp-when-not-emptyp-forward-chaining
  (implies (not (emptyp set))
           (setp set))
  :rule-classes :forward-chaining
  :enable emptyp)

;; TODO: Should this also be a regular rewrite rule?
(defrule emptyp-when-not-setp-forward-chaining
  (implies (not (setp set))
           (emptyp set))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define head ((set setp))
  :parents (set)
  :short "Get an element of the nonempty @(see set)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, returns @('nil').")
   (xdoc::p
     "From a user perspective, this should likely be viewed as an arbitrary
      element of the set, to be used only in conjunction with @(tsee left) and
      @(tsee right) to fold over the set. Under the hood, this is the root
      element of the underlying tree, which will be the unique maximum value
      with respect to @(tsee heap<)."))
  (tree-head (sfix set))
  :no-function t
  :inline t)

(defrule head-when-set-equiv
  (implies (set-equiv x y)
           (equal (head x)
                  (head y)))
  :rule-classes :congruence
  :enable (head
           set-equiv))

(defruled head-when-emptyp
  (implies (emptyp set)
           (equal (head set)
                  nil))
  :enable head)

(defrule head-when-emptyp-cheap
  (implies (emptyp set)
           (equal (head set)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable head-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define left ((set setp))
  :returns (left setp)
  :parents (set)
  :short "Get the \"left\" subset of the nonempty @(see set)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty sets, returns @('nil').")
   (xdoc::p
     "From a user perspective, this should likely be viewed as an arbitrary
      proper subset excluding the @(tsee head) and disjoint from the @(tsee
      right) subset. Concretely, it is the subset for which all elements are
      @(tsee bst<) the @(tsee head). In terms of the underlying tree
      representation, this is the left subtree."))
  (tree-left (sfix set))
  :no-function t
  :inline t)

(defrule left-type-prescription
  (setp (left set))
  :rule-classes ((:type-prescription :typed-term (left set))))

(defruled left-when-emptyp
  (implies (emptyp set)
           (equal (left set)
                  nil))
  :enable left)

(defrule left-when-emptyp-cheap
  (implies (emptyp set)
           (equal (left set)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable left-when-emptyp)

(defrule emptyp-when-not-emptyp-of-left-forward-chaining
  (implies (not (emptyp (left set)))
           (not (emptyp set)))
  :rule-classes :forward-chaining)

(defrule equal-of-left-of-arg2-when-setp
  ;; TODO: Does this trigger on the symmetric equality form? I think so.
  (implies (setp x)
           (equal (equal (left x) x)
                  (emptyp x)))
  :enable (left
           emptyp))

(defrule acl2-count-of-left-linear
  (<= (acl2-count (left set))
      (acl2-count set))
  :rule-classes :linear
  :enable (left
           sfix))

(defrule acl2-count-of-left-when-not-emptyp-linear
  (implies (not (emptyp set))
           (< (acl2-count (left set))
              (acl2-count set)))
  :rule-classes :linear
  :enable (emptyp
           left
           sfix))

(defrule bst<-of-head-of-left-and-head
  (implies (not (emptyp (left set)))
           (bst< (head (left set))
                 (head set)))
  :enable (head
           left
           emptyp
           sfix
           setp))

(defrule heap<-of-head-of-left-and-head
  (implies (and (not (emptyp (left tree))))
           (heap< (head (left tree))
                  (head tree)))
  :enable (head
           left
           emptyp
           sfix
           setp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define right ((set setp))
  :returns (right setp)
  :parents (set)
  :short "Get the \"right\" subset of the nonempty @(see set)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty sets, returns @('nil').")
   (xdoc::p
     "From a user perspective, this should likely be viewed as an arbitrary
      proper subset excluding the @(tsee head) and disjoint from the @(tsee
      left) subset. Concretely, it is the subset for which the @(tsee head) is
      @(tsee bst<) all elements. In terms of the underlying tree representation,
      this is the right subtree."))
  (tree-right (sfix set))
  :no-function t
  :inline t)

(defrule right-type-prescription
  (setp (right set))
  :rule-classes ((:type-prescription :typed-term (right set))))

(defruled right-when-emptyp
  (implies (emptyp set)
           (equal (right set)
                  nil))
  :enable right)

(defrule right-when-emptyp-cheap
  (implies (emptyp set)
           (equal (right set)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable right-when-emptyp)

(defrule emptyp-when-not-emptyp-of-right-forward-chaining
  (implies (not (emptyp (right set)))
           (not (emptyp set)))
  :rule-classes :forward-chaining)

(defrule equal-of-right-of-arg2-when-setp
  ;; TODO: Does this trigger on the symmetric equality form? I think so.
  (implies (setp x)
           (equal (equal (right x) x)
                  (emptyp x)))
  :enable (right
           emptyp))

(defrule acl2-count-of-right-linear
  (<= (acl2-count (right set))
      (acl2-count set))
  :rule-classes :linear
  :enable (right
           sfix))

(defrule acl2-count-of-right-when-not-emptyp-linear
  (implies (not (emptyp set))
           (< (acl2-count (right set))
              (acl2-count set)))
  :rule-classes :linear
  :enable (emptyp
           right
           sfix))

(defrule bst<-of-head-and-head-of-right
  (implies (not (emptyp (right set)))
           (bst< (head set)
                 (head (right set))))
  :enable (head
           right
           emptyp
           sfix
           setp))

(defrule heap<-of-head-and-head-of-right
  (implies (and (not (emptyp (right tree))))
           (heap< (head (right tree))
                  (head tree)))
  :enable (head
           right
           emptyp
           sfix
           setp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule setp-of-tree-node
  (equal (setp (tree-node head left right))
         (and (setp (tree-fix left))
              (setp (tree-fix right))
              (bst<-all-l left head)
              (bst<-all-r head right)
              (heap<-all-l left head)
              (heap<-all-l right head)))
  :enable (setp
           bst-p
           heapp
           sfix
           head
           left
           right
           emptyp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define set-induct (set)
  :parents (set)
  :short "Induct over the structure of a set."
  (or (emptyp set)
      (let ((left (set-induct (left set)))
            (right (set-induct (right set))))
        (declare (ignore left right))
        t))
  :no-function t
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards nil)

(in-theory (enable (:i set-induct)))

(defruled set-induction
  t
  :rule-classes
  ((:induction :pattern (setp set)
               :scheme (set-induct set))))

(defruled nonempty-set-induction
  t
  :rule-classes
  ((:induction :pattern (not (emptyp set))
               :scheme (set-induct set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define set-bi-induct (x y)
  :parents (set)
  :short "Induct over the structure of two sets simultaneously."
  (or (emptyp x)
      (emptyp y)
      (let ((left (set-bi-induct (left x) (left y)))
            (right (set-bi-induct (right x) (right y))))
        (declare (ignore left right))
        t))
  :no-function t
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards nil)

(in-theory (enable (:i set-bi-induct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define to-list
  ((set setp))
  :returns (list true-listp)
  :parents (set)
  :short "Create a list of values from a set."
  (tree-post-order (sfix set)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: theorems
;; - no-duplicatesp
;; - connect member-equal to in under iff
;; - empty to null

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: to-oset
;; (With the current bst<, this is just an in-order traversal.)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy set-extra-rules
  '(sfix-when-not-setp
    sfix-when-emptyp
    head-when-emptyp
    left-when-emptyp
    right-when-emptyp
    set-induction
    nonempty-set-induction))
