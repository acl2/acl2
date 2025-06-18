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
(include-book "join-defs")
(include-book "set-defs")
(include-book "split-defs")
(include-book "subset-defs")
(include-book "union-defs")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "binary-tree"))
(local (include-book "bst"))
(local (include-book "bst-order"))
(local (include-book "double-containment"))
(local (include-book "heap"))
(local (include-book "heap-order"))
(local (include-book "in"))
(local (include-book "join"))
(local (include-book "pick-a-point"))
(local (include-book "set"))
(local (include-book "split"))
(local (include-book "subset"))
(local (include-book "union"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-diff
  ((x binary-tree-p)
   (y binary-tree-p))
  :parents (implementation)
  :short "Take the difference of two treaps."
  :returns (tree binary-tree-p)
  (cond ((or (tree-emptyp x)
             (tree-emptyp y))
         (tree-fix x))
        ((heap< (tree-head x)
                (tree-head y))
         (b* (((mv - left right)
               (tree-split (tree-head y) x))
              (left (tree-diff left (tree-left y)))
              (right (tree-diff right (tree-right y))))
           (tree-join-at (tree-head y) left right)))
        (t
          (b* (((mv in left right)
                (tree-split (tree-head x) y))
               (left (tree-diff (tree-left x) left))
               (right (tree-diff (tree-right x) right)))
            (if (not in)
                (tree-node (tree-head x) left right)
              (tree-join-at (tree-head x) left right)))))
  :measure (+ (acl2-count x)
              (acl2-count y))
  :hints (("Goal" :in-theory (enable o-p o< o-finp)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-diff-type-prescription
  (or (consp (tree-diff x y))
      (equal (tree-diff x y) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-diff)

(defrule tree-diff-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv x y)
           (equal (tree-diff x z)
                  (tree-diff y z)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((tree-diff x z)
           (tree-diff y z)))

(defrule tree-diff-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv y z)
           (equal (tree-diff x y)
                  (tree-diff x z)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((tree-diff x y)
           (tree-diff x z)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-emptyp-of-tree-diff-when-tree-emptyp-of-arg1
  (implies (tree-emptyp x)
           (tree-emptyp (tree-diff x y)))
  :enable tree-diff)

(defrule tree-emptyp-of-tree-diff-when-tree-emptyp-of-arg2
  (implies (tree-emptyp y)
           (equal (tree-diff x y)
                  (tree-fix x)))
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-tree-diff
  (implies (and (bst-p x)
                (bst-p y))
           (equal (tree-in a (tree-diff x y))
                  (and (tree-in a x)
                       (not (tree-in a y)))))
  :induct t
  :enable (tree-diff
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-tree-diff-when-bst<-all-l-of-arg1
  (implies (bst<-all-l x a)
           (bst<-all-l (tree-diff x y) a))
  :induct t
  :enable tree-diff)

(defrule bst<-all-r-of-arg1-and-tree-diff-when-bst-<-all-r-of-arg1-and-arg2
  (implies (bst<-all-r a x)
           (bst<-all-r a (tree-diff x y)))
  :induct t
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst-p-of-tree-diff-when-bst-p
  (implies (and (bst-p x)
                (bst-p y))
           (bst-p (tree-diff x y)))
  :induct t
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-diff
  (implies (heap<-all-l x a)
           (heap<-all-l (tree-diff x y) a))
  :induct t
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-diff-when-bst-p-and-heapp
  (implies (and (bst-p x)
                (bst-p y)
                (heapp x)
                (heapp y))
           (heapp (tree-diff x y)))
  :induct t
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule setp-of-tree-diff-when-setp
  (implies (and (setp x)
                (setp y))
           (setp (tree-diff x y)))
  :enable setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define diff
  ((x setp)
   (y setp))
  :returns (set setp)
  :parents (set)
  :short "Set difference."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(n\\log(m/n))$) (where @($n < m$))."))
  (tree-diff (sfix x) (sfix y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule diff-when-set-equiv-of-arg1-congruence
  (implies (set-equiv x y)
           (equal (diff x z)
                  (diff y z)))
  :rule-classes :congruence
  :enable set-equiv
  :expand ((diff x z)
           (diff y z)))

(defrule diff-when-set-equiv-of-arg2-congruence
  (implies (set-equiv y z)
           (equal (diff x y)
                  (diff x z)))
  :rule-classes :congruence
  :enable set-equiv
  :expand ((diff x y)
           (diff x z)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-diff-when-emptyp-of-arg1
  (implies (emptyp x)
           (emptyp (diff x y)))
  :enable (diff
           emptyp))

(defrule emptyp-of-diff-when-tree-emptyp-of-arg2
  (implies (emptyp y)
           (equal (diff x y)
                  (sfix x)))
  :enable (diff
           emptyp
           sfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule in-of-diff
  (equal (in a (diff x y))
         (and (in a x)
              (not (in a y))))
  :enable (diff
           in
           sfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-diff-when-bst<-all-l-of-arg1
  (implies (bst<-all-l (sfix x) a)
           (bst<-all-l (diff x y) a))
  :enable diff)

(defrule bst<-all-r-of-arg1-and-diff-when-bst-<-all-r-of-arg1-and-arg2
  (implies (bst<-all-r a (sfix x))
           (bst<-all-r a (diff x y)))
  :enable diff)

(defrule heap<-all-l-of-diff
  (implies (heap<-all-l (sfix x) a)
           (heap<-all-l (diff x y) a))
  :enable diff)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule subset-of-diff
  (subset (diff x y) x)
  :enable (pick-a-point
           subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: enable in general?
(defruled diff-of-diff-becomes-diff-of-union
  (equal (diff (diff x y) z)
         (diff x (union y z)))
  :enable (double-containment
           pick-a-point
           subset))
