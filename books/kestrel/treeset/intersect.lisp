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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-intersect
  ((x binary-tree-p)
   (y binary-tree-p))
  (declare (xargs :type-prescription (or (consp (tree-intersect x y))
                                         (equal (tree-intersect x y) nil))))
  :parents (implementation)
  :short "Take the intersection of two treaps."
  :long
  (xdoc::topstring
   (xdoc::p
     "The result might not be a intersection if the input trees are not binary search
      trees."))
  :returns (tree binary-tree-p)
  (cond ((or (tree-emptyp x)
             (tree-emptyp y))
         nil)
        ((heap< (tree-head x)
                (tree-head y))
         (b* (((mv in left right)
               (tree-split (tree-head y) x))
              (left (tree-intersect left (tree-left y)))
              (right (tree-intersect right (tree-right y))))
           (if in
               (tree-node (tree-head y) left right)
             (tree-join-at (tree-head y) left right))))
        (t
          (b* (((mv in left right)
                (tree-split (tree-head x) y))
               (left (tree-intersect (tree-left x) left))
               (right (tree-intersect (tree-right x) right)))
            (if in
                (tree-node (tree-head x) left right)
              (tree-join-at (tree-head x) left right)))))
  :measure (+ (acl2-count x)
              (acl2-count y))
  :hints (("Goal" :in-theory (enable o-p o< o-finp)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-intersect-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv x y)
           (equal (tree-intersect x z)
                  (tree-intersect y z)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((tree-intersect x z)
           (tree-intersect y z)))

(defrule tree-intersect-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv y z)
           (equal (tree-intersect x y)
                  (tree-intersect x z)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((tree-intersect x y)
           (tree-intersect x z)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-emptyp-of-tree-intersect-when-tree-emptyp-of-arg1
  (implies (tree-emptyp x)
           (tree-emptyp (tree-intersect x y)))
  :enable tree-intersect)

(defrule tree-emptyp-of-tree-intersect-when-tree-emptyp-of-arg2
  (implies (tree-emptyp y)
           (tree-emptyp (tree-intersect x y)))
  :enable tree-intersect)

(defrule tree-in-of-tree-intersect
  (implies (and (bst-p x)
                (bst-p y))
           (equal (tree-in a (tree-intersect x y))
                  (and (tree-in a x)
                       (tree-in a y))))
  :induct t
  :enable (tree-intersect
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-tree-intersect
  (implies (and (bst<-all-l x z)
                (bst<-all-l y z))
           (bst<-all-l (tree-intersect x y) z))
  :induct t
  :enable tree-intersect)

(defrule bst<-all-r-of-arg1-and-tree-intersect
  (implies (and (bst<-all-r x y)
                (bst<-all-r x z))
           (bst<-all-r x (tree-intersect y z)))
  :induct t
  :enable tree-intersect)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst-p-of-tree-intersect-when-bst-p
  (implies (and (bst-p x)
                (bst-p y))
           (bst-p (tree-intersect x y)))
  :induct t
  :enable tree-intersect)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-intersect
  (implies (and (heap<-all-l x z)
                (heap<-all-l y z))
           (heap<-all-l (tree-intersect x y) z))
  :induct t
  :enable tree-intersect)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-intersect-when-bst-p-and-heapp
  (implies (and (bst-p x)
                (bst-p y)
                (heapp x)
                (heapp y))
           (heapp (tree-intersect x y)))
  :induct t
  :enable (tree-intersect
           tree-head-when-heapp-and-tree-in-tree-head-syntaxp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule setp-of-tree-intersect-when-setp
  (implies (and (setp x)
                (setp y))
           (setp (tree-intersect x y)))
  :enable setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection intersect
  :parents (set)
  :short "An @($n$)-ary set intersection."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(n\\log(m/n))$) (for binary intersection, where @($n < m$))."))

  (define binary-intersect
    ((x setp)
     (y setp))
    :returns (set setp)
    (tree-intersect (sfix x) (sfix y))
    :no-function t
    :inline t)

  ;;;;;;;;;;;;;;;;;;;;

  (define intersect-macro-loop
    ((list true-listp))
    :guard (and (consp list)
                (consp (rest list)))
    (if (endp (rest (rest list)))
        (list 'binary-intersect
              (first list)
              (second list))
      (list 'binary-intersect
            (first list)
            (intersect-macro-loop (rest list))))
    :hints (("Goal" :in-theory (enable o< o-finp acl2-count))))

  (defmacro intersect (x y &rest rst)
    (declare (xargs :guard t))
    (intersect-macro-loop (list* x y rst)))

  (add-macro-fn intersect binary-intersect$inline t)

  "@(def intersect)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule intersect-when-set-equiv-of-arg1-congruence
  (implies (set-equiv x y)
           (equal (intersect x z)
                  (intersect y z)))
  :rule-classes :congruence
  :enable (set-equiv
           intersect))

(defrule intersect-when-set-equiv-of-arg2-congruence
  (implies (set-equiv y z)
           (equal (intersect x y)
                  (intersect x z)))
  :rule-classes :congruence
  :enable (set-equiv
           intersect))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-intersect-when-emptyp-of-arg1
  (implies (emptyp x)
           (emptyp (intersect x y)))
  :enable (emptyp
           intersect))

(defrule emptyp-of-intersect-when-emptyp-of-arg2
  (implies (emptyp y)
           (emptyp (intersect x y)))
  :enable (emptyp
           intersect))

(defrule in-of-intersect
  (equal (in a (intersect x y))
         (and (in a x)
              (in a y)))
  :enable (intersect
           in
           sfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-intersect
  (implies (and (bst<-all-l x z)
                (bst<-all-l y z))
           (bst<-all-l (intersect x y) z))
  :enable (intersect
           sfix))

(defrule bst<-all-r-of-arg1-and-intersect
  (implies (and (bst<-all-r x y)
                (bst<-all-r x z))
           (bst<-all-r x (intersect y z)))
  :enable (intersect
           sfix))

(defrule heap<-all-l-of-intersect
  (implies (and (heap<-all-l x z)
                (heap<-all-l y z))
           (heap<-all-l (intersect x y) z))
  :enable (intersect
           sfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: better names?

(defrule subset-of-intersect-left
  (subset (intersect x y) x)
  :enable (pick-a-point
           subset))

(defrule subset-of-intersect-right
  (subset (intersect x y) y)
  :enable (pick-a-point
           subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule associativity-of-intersect
  (equal (intersect (intersect x y) z)
         (intersect x y z))
  :enable (double-containment
           pick-a-point
           subset))

(defrule commutativity-of-intersect
  (equal (intersect y x)
         (intersect x y))
  :enable (double-containment
           pick-a-point
           subset))
