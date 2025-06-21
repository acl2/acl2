; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "binary-tree-defs")
(include-book "bst-order-defs")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "binary-tree"))
(local (include-book "bst-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bst<-all-l
  ((tree binary-tree-p)
   x)
  (declare (xargs :type-prescription (booleanp (bst<-all-l tree x))))
  :parents (binary-tree)
  :short "Check that all members of a tree are @(tsee bst<) some value."
  (or (tree-emptyp tree)
      (and (bst< (tree-head tree) x)
           (bst<-all-l (tree-left tree) x)
           (bst<-all-l (tree-right tree) x)))
  :hints (("Goal" :in-theory (enable o< o-finp))))

(define bst<-all-r
  (x
   (tree binary-tree-p))
  (declare (xargs :type-prescription (booleanp (bst<-all-r x tree))))
  :parents (binary-tree)
  :short "Check that some value is @(tsee bst<) all members of a tree."
  (or (tree-emptyp tree)
      (and (bst< x (tree-head tree))
           (bst<-all-r x (tree-left tree))
           (bst<-all-r x (tree-right tree))))
  :hints (("Goal" :in-theory (enable o< o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (bst<-all-l x a)
                  (bst<-all-l y a)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((bst<-all-l x a)
           (bst<-all-l y a)))

(defrule bst<-all-r-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (bst<-all-r a x)
                  (bst<-all-r a y)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((bst<-all-r a x)
           (bst<-all-r a y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-nil
  (bst<-all-l nil tree)
  :enable bst<-all-l)

(defrule bst<-all-r-of-arg1-and-nil
  (bst<-all-r tree nil)
  :enable bst<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-when-tree-emptyp
  (implies (tree-emptyp tree)
           (bst<-all-l tree x))
  :enable bst<-all-l)

(defruled bst<-all-l-when-tree-emptyp-cheap
  (implies (tree-emptyp tree)
           (bst<-all-l tree x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst<-all-l-when-tree-emptyp)

(defruled bst<-all-r-when-tree-emptyp
  (implies (tree-emptyp tree)
           (bst<-all-r x tree))
  :enable bst<-all-r)

(defruled bst<-all-r-when-tree-emptyp-cheap
  (implies (tree-emptyp tree)
           (bst<-all-r x tree))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst<-all-r-when-tree-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-when-bst<-all-r
  (implies (bst<-all-r x tree)
           (equal (bst<-all-l tree x)
                  (tree-emptyp tree)))
  :induct t
  :enable (bst<-all-r
           bst<-all-l
           bst<-rules))

(defruled bst<-all-l-when-bst<-all-r-forward-chaining
  (implies (bst<-all-r x tree)
           (equal (bst<-all-l tree x)
                  (tree-emptyp tree)))
  :rule-classes :forward-chaining
  :enable bst<-all-l-when-bst<-all-r)

(defrule bst<-all-l-when-bst<-all-r-and-not-tree-emptyp-forward-chaining
  (implies (and (bst<-all-r x tree)
                (not (tree-emptyp tree)))
           (not (bst<-all-l tree x)))
  :rule-classes :forward-chaining
  :enable bst<-all-l-when-bst<-all-r)

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-r-when-bst<-all-l
  (implies (bst<-all-l tree x)
           (equal (bst<-all-r x tree)
                  (tree-emptyp tree)))
  :induct t
  :enable (bst<-all-l
           bst<-all-r
           bst<-rules))

(defruled bst<-all-r-when-bst<-all-l-forward-chaining
  (implies (bst<-all-l tree x)
           (equal (bst<-all-r x tree)
                  (tree-emptyp tree)))
  :rule-classes :forward-chaining
  :enable bst<-all-r-when-bst<-all-l)

(defrule bst<-all-r-when-bst<-all-l-and-not-tree-emptyp-forward-chaining
  (implies (and (bst<-all-l tree x)
                (not (tree-emptyp tree)))
           (not (bst<-all-r x tree)))
  :rule-classes :forward-chaining
  :enable bst<-all-r-when-bst<-all-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-emptyp-when-not-bst<-all-l-forward-chaining
  (implies (not (bst<-all-l tree x))
           (not (tree-emptyp tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst<-all-l)

(defrule tree-emptyp-when-not-bst<-all-r-forward-chaining
  (implies (not (bst<-all-r x tree))
           (not (tree-emptyp tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-arg1-and-tree-head
  (equal (bst<-all-l tree (tree-head tree))
         (tree-emptyp tree))
  :enable (bst<-all-l
           tree-head
           bst<-rules))

(defrule bst<-all-r-of-tree-head
  (equal (bst<-all-r (tree-head tree) tree)
         (tree-emptyp tree))
  :enable (bst<-all-r
           tree-head
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-of-tree-left-when-bst<-all-l
  (implies (bst<-all-l tree x)
           (bst<-all-l (tree-left tree) x))
  :enable bst<-all-l)

(defrule bst<-all-l-of-tree-left-when-bst<-all-l-cheap
  (implies (bst<-all-l tree x)
           (bst<-all-l (tree-left tree) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst<-all-l-of-tree-left-when-bst<-all-l)

(defruled bst<-all-l-of-tree-right-when-bst<-all-l
  (implies (bst<-all-l tree x)
           (bst<-all-l (tree-right tree) x))
  :enable bst<-all-l)

(defrule bst<-all-l-of-tree-right-when-bst<-all-l-cheap
  (implies (bst<-all-l tree x)
           (bst<-all-l (tree-right tree) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst<-all-l-of-tree-right-when-bst<-all-l)

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-r-of-arg1-and-tree-left-when-bst<-all-r
  (implies (bst<-all-r x tree)
           (bst<-all-r x (tree-left tree)))
  :enable bst<-all-r)

(defrule bst<-all-r-of-arg1-and-tree-left-when-bst<-all-r-cheap
  (implies (bst<-all-r x tree)
           (bst<-all-r x (tree-left tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst<-all-r-of-arg1-and-tree-left-when-bst<-all-r)

(defruled bst<-all-r-of-arg1-and-tree-right-when-bst<-all-r
  (implies (bst<-all-r x tree)
           (bst<-all-r x (tree-right tree)))
  :enable bst<-all-r)

(defrule bst<-all-r-of-arg1-and-tree-right-when-bst<-all-r-cheap
  (implies (bst<-all-r x tree)
           (bst<-all-r x (tree-right tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst<-all-r-of-arg1-and-tree-right-when-bst<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-tree-node
  (equal (bst<-all-l (tree-node head left right) x)
         (and (bst< head x)
              (bst<-all-l left x)
              (bst<-all-l right x)))
  :enable bst<-all-l)

(defrule bst<-all-r-of-arg1-and-tree-node
  (equal (bst<-all-r x (tree-node head left right))
         (and (bst< x head)
              (bst<-all-r x left)
              (bst<-all-r x right)))
  :enable bst<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-l-weaken
  (implies (and (bst< x y)
                (bst<-all-l tree x))
           (bst<-all-l tree y))
  :induct t
  :enable (bst<-all-l
           bst<-rules))

(defruled bst<-all-l-weaken2
  (implies (and (not (bst< x y))
                (bst<-all-l tree y))
           (bst<-all-l tree x))
  :enable (bst<-all-l-weaken
           bst<-rules)
  :disable bst<-trichotomy
  :use ((:instance bst<-trichotomy
                   (x y)
                   (y x))))

;;;;;;;;;;;;;;;;;;;;

(defruled bst<-all-r-weaken
  (implies (and (bst< x y)
                (bst<-all-r y tree))
           (bst<-all-r x tree))
  :induct t
  :enable (bst<-all-r
           bst<-rules))

(defruled bst<-all-r-weaken2
  (implies (and (not (bst< x y))
                (bst<-all-r x tree))
           (bst<-all-r y tree))
  :enable (bst<-all-r-weaken
            bst<-rules)
  :disable bst<-trichotomy
  :use ((:instance bst<-trichotomy
                   (x y)
                   (y x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-of-tree-head-when-bst<-all-l
  (implies (and (bst<-all-l tree x)
                (not (tree-emptyp tree)))
           (bst< (tree-head tree) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :enable bst<-all-l)

(defrule bst<-of-arg1-and-tree-head-when-bst<-all-r-arg1
  (implies (and (bst<-all-r x tree)
                (not (tree-emptyp tree)))
           (bst< x (tree-head tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :enable bst<-all-r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bst-p
  ((tree binary-tree-p))
  (declare (xargs :type-prescription (booleanp (bst-p tree))))
  :parents (binary-tree)
  :short "Check the binary search tree property."
  :long
  (xdoc::topstring
   (xdoc::p
     "This recognizer is currently inefficient, operating in @($O(n^2)$) time
      instead of @($O(n)$). Eventually we hope to add an @(tsee mbe) with a
      linear-time executable version."))
  (or (tree-emptyp tree)
      (and (bst-p (tree-left tree))
           (bst-p (tree-right tree))
           (bst<-all-l (tree-left tree) (tree-head tree))
           (bst<-all-r (tree-head tree) (tree-right tree))))
  :hints (("Goal" :in-theory (enable o< o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst-p-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (bst-p x)
                  (bst-p y)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((bst-p x)
           (bst-p y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst-p-of-tree-left-when-tree-orderdp
  (implies (bst-p tree)
           (bst-p (tree-left tree)))
  :enable bst-p)

(defrule bst-p-of-tree-left-when-tree-orderdp-cheap
  (implies (bst-p tree)
           (bst-p (tree-left tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst-p-of-tree-left-when-tree-orderdp)

(defruled bst-p-of-tree-right-when-bst-p
  (implies (bst-p tree)
           (bst-p (tree-right tree)))
  :enable bst-p)

(defrule bst-p-of-tree-right-when-bst-p-cheap
  (implies (bst-p tree)
           (bst-p (tree-right tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst-p-of-tree-right-when-bst-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst-p-when-tree-emptyp
  (implies (tree-emptyp tree)
           (bst-p tree))
  :enable bst-p)

(defrule bst-p-when-tree-emptyp-cheap
  (implies (tree-emptyp tree)
           (bst-p tree))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst-p-when-not-tree-emptyp
  (implies (not (tree-emptyp tree))
           (equal (bst-p tree)
                  (and (bst-p (tree-left tree))
                       (bst-p (tree-right tree))
                       (bst<-all-l (tree-left tree) (tree-head tree))
                       (bst<-all-r (tree-head tree) (tree-right tree)))))
  :enable bst-p)

(defruled bst-p-when-not-tree-emptyp-cheap
  (implies (not (tree-emptyp tree))
           (equal (bst-p tree)
                  (and (bst-p (tree-left tree))
                       (bst-p (tree-right tree))
                       (bst<-all-l (tree-left tree) (tree-head tree))
                       (bst<-all-r (tree-head tree) (tree-right tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable bst-p-when-not-tree-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst-p-of-tree-node
  (equal (bst-p (tree-node head left right))
         (and (bst-p left)
              (bst-p right)
              (bst<-all-l left head)
              (bst<-all-r head right)))
  :enable bst-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bst<-of-tree-head-tree-left-and-tree-head
  (implies (and (bst-p tree)
                (not (tree-emptyp (tree-left tree))))
           (bst< (tree-head (tree-left tree))
                 (tree-head tree))))

(defruled bst<-of-tree-head-and-tree-head-tree-right
  (implies (and (bst-p tree)
                (not (tree-emptyp (tree-right tree))))
           (bst< (tree-head tree)
                 (tree-head (tree-right tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-tree-left-and-tree-head-when-bst-p
  (implies (bst-p set)
           (bst<-all-l (tree-left set)
                       (tree-head set))))

(defrule bst<-all-r-of-tree-head-and-tree-right-when-bst-p
  (implies (bst-p tree)
           (bst<-all-r (tree-head tree)
                       (tree-right tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy bst<-all-extra-rules
  '(bst<-all-l-when-tree-emptyp
    bst<-all-r-when-tree-emptyp
    bst<-all-l-when-bst<-all-r-forward-chaining
    bst<-all-r-when-bst<-all-l-forward-chaining
    bst<-all-l-of-tree-left-when-bst<-all-l
    bst<-all-l-of-tree-right-when-bst<-all-l
    bst<-all-r-of-arg1-and-tree-left-when-bst<-all-r
    bst<-all-r-of-arg1-and-tree-right-when-bst<-all-r
    bst<-all-l-weaken
    bst<-all-l-weaken2
    bst<-all-r-weaken
    bst<-all-r-weaken2))

(defthy bst-p-extra-rules
  '(bst-p-of-tree-left-when-tree-orderdp
    bst-p-of-tree-right-when-bst-p
    bst-p-when-tree-emptyp
    bst-p-when-not-tree-emptyp
    bst<-of-tree-head-tree-left-and-tree-head
    bst<-of-tree-head-and-tree-head-tree-right))
