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

(include-book "cardinality-defs")
(include-book "in-defs")
(include-book "insert-defs")
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
(local (include-book "cardinality"))
(local (include-book "double-containment"))
(local (include-book "heap"))
(local (include-book "heap-order"))
(local (include-book "in"))
(local (include-book "insert"))
(local (include-book "pick-a-point"))
(local (include-book "set"))
(local (include-book "split"))
(local (include-book "subset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-union
  ((x binary-tree-p)
   (y binary-tree-p))
  :parents (implementation)
  :short "Take the union of two treaps."
  :long
  (xdoc::topstring
   (xdoc::p
     "The result might not be a union if the input trees are not binary search
      trees."))
  :returns (tree binary-tree-p)
  (cond ((tree-emptyp x)
         (tree-fix y))
        ((tree-emptyp y)
         (tree-fix x))
        ((heap< (tree-head x)
             (tree-head y))
         (b* (((mv - left right)
               (tree-split (tree-head y) x)))
           (tree-node (tree-head y)
                      (tree-union left (tree-left y))
                      (tree-union right (tree-right y)))))
        (t (b* (((mv - left right)
                 (tree-split (tree-head x) y)))
             (tree-node (tree-head x)
                        (tree-union (tree-left x) left)
                        (tree-union (tree-right x) right)))))
  :measure (+ (acl2-count x)
              (acl2-count y))
  :hints (("Goal" :in-theory (enable o-p o< o-finp)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-union-type-prescription
  (or (consp (tree-union x y))
      (equal (tree-union x y) nil))
  :rule-classes :type-prescription
  :induct t
  :enable (tree-union
           tree-fix))

(defrule tree-union-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv x y)
           (equal (tree-union x z)
                  (tree-union y z)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((tree-union x z)
           (tree-union y z)))

(defrule tree-union-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv y z)
           (equal (tree-union x y)
                  (tree-union x z)))
  :rule-classes :congruence
  :enable tree-equiv
  :expand ((tree-union x y)
           (tree-union x z)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-emptyp-of-tree-union
  (equal (tree-emptyp (tree-union x y))
         (and (tree-emptyp x)
              (tree-emptyp y)))
  :induct t
  :enable tree-union)

(defrule tree-in-of-tree-union
  (implies (and (bst-p x)
                (bst-p y))
           (equal (tree-in a (tree-union x y))
                  (or (tree-in a x)
                      (tree-in a y))))
  :induct t
  :enable (tree-union
           bst<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-tree-union
  (equal (bst<-all-l (tree-union x y) z)
         (and (bst<-all-l x z)
              (bst<-all-l y z)))
  ;; TODO: better proof?
  :use lemma
  :prep-lemmas
  ((defruled lemma
     (iff (bst<-all-l (tree-union x y) z)
          (and (bst<-all-l x z)
               (bst<-all-l y z)))
     :induct t
     :enable (tree-union
              tree-split-extra-rules))))

(defrule bst<-all-r-of-arg1-and-tree-union
  (equal (bst<-all-r x (tree-union y z))
         (and (bst<-all-r x y)
              (bst<-all-r x z)))
  :use lemma
  :prep-lemmas
  ((defruled lemma
     (iff (bst<-all-r x (tree-union y z))
          (and (bst<-all-r x y)
               (bst<-all-r x z)))
     :induct t
     :enable (tree-union
              tree-split-extra-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst-p-of-tree-union-when-bst-p
  (implies (and (bst-p x)
                (bst-p y))
           (bst-p (tree-union x y)))
  :induct t
  :enable tree-union)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-union
  (equal (heap<-all-l (tree-union x y) z)
         (and (heap<-all-l x z)
              (heap<-all-l y z)))
  :use lemma
  :prep-lemmas
  ((defruled lemma
     (iff (heap<-all-l (tree-union x y) z)
          (and (heap<-all-l x z)
               (heap<-all-l y z)))
     :induct t
     :enable (tree-union
              tree-split-extra-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()
  (defrulel lemma0
    (implies (and (not (heap< (tree-head x) (tree-head y)))
                  (heap<-all-l (tree-left y) (tree-head y))
                  (heap<-all-l (tree-right y) (tree-head y)))
             (heap<-all-l (mv-nth 1 (tree-split (tree-head x) y))
                          (tree-head x)))
    :enable (heap<-all-l-extra-rules
             tree-split-extra-rules)
    :disable heap<-trichotomy
    :use ((:instance heap<-trichotomy
                     (x (tree-head y))
                     (y (tree-head x)))))

  (defrulel lemma1
    (implies (and (not (heap< (tree-head x) (tree-head y)))
                  (heap<-all-l (tree-left y) (tree-head y))
                  (heap<-all-l (tree-right y) (tree-head y)))
             (heap<-all-l (mv-nth 2 (tree-split (tree-head x) y))
                          (tree-head x)))
    :enable (heap<-all-l-extra-rules
             tree-split-extra-rules)
    :disable heap<-trichotomy
    :use ((:instance heap<-trichotomy
                     (x (tree-head y))
                     (y (tree-head x)))))

  (defrulel lemma2
    (implies (and (heap< (tree-head x) (tree-head y))
                  (heap<-all-l (tree-left x) (tree-head x))
                  (heap<-all-l (tree-right x) (tree-head x)))
             (heap<-all-l (mv-nth 1 (tree-split (tree-head y) x))
                          (tree-head y)))
    :enable (heap<-all-l-extra-rules
             tree-split-extra-rules))

  (defrulel lemma3
    (implies (and (heap< (tree-head x) (tree-head y))
                  (heap<-all-l (tree-left x) (tree-head x))
                  (heap<-all-l (tree-right x) (tree-head x)))
             (heap<-all-l (mv-nth 2 (tree-split (tree-head y) x))
                          (tree-head y)))
    :enable (heap<-all-l-extra-rules
             tree-split-extra-rules))

  (defrule heapp-of-tree-union-when-heapp
    (implies (and (heapp x)
                  (heapp y))
             (heapp (tree-union x y)))
    :induct t
    :enable tree-union))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule setp-of-tree-union-when-setp
  (implies (and (setp x)
                (setp y))
           (setp (tree-union x y)))
  :enable setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection union
  :parents (set)
  :short "An @($n$)-ary set union."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(n\\log(m/n))$) (for binary union, where @($n < m$))."))

  (define binary-union
    ((x setp)
     (y setp))
    :returns (set setp)
    (tree-union (sfix x) (sfix y))
    :inline t)

  ;;;;;;;;;;;;;;;;;;;;

  (define union-macro-loop
    ((list true-listp))
    :guard (and (consp list)
                (consp (rest list)))
    (if (endp (rest (rest list)))
        (list 'binary-union
              (first list)
              (second list))
      (list 'binary-union
            (first list)
            (union-macro-loop (rest list))))
    :hints (("Goal" :in-theory (enable o< o-finp acl2-count))))

  (defmacro union (x y &rest rst)
    (declare (xargs :guard t))
    (union-macro-loop (list* x y rst)))

  (add-macro-fn union binary-union$inline t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule union-when-set-equiv-of-arg1-congruence
  (implies (set-equiv x y)
           (equal (union x z)
                  (union y z)))
  :rule-classes :congruence
  :enable (set-equiv
           union))

(defrule union-when-set-equiv-of-arg2-congruence
  (implies (set-equiv y z)
           (equal (union x y)
                  (union x z)))
  :rule-classes :congruence
  :enable (set-equiv
           union))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-union
  (equal (emptyp (union x y))
         (and (emptyp x)
              (emptyp y)))
  :enable (union
           emptyp))

(defrule in-of-union
  (equal (in a (union x y))
         (or (in a x)
             (in a y)))
  :enable (union
           in
           sfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-union
  (equal (bst<-all-l (union x y) z)
         (and (bst<-all-l (sfix x) z)
              (bst<-all-l (sfix y) z)))
  :enable union)

(defrule bst<-all-r-of-arg1-and-union
  (equal (bst<-all-r x (union y z))
         (and (bst<-all-r x (sfix y))
              (bst<-all-r x (sfix z))))
  :enable union)

(defrule heap<-all-l-of-union
  (equal (heap<-all-l (union x y) z)
         (and (heap<-all-l (sfix x) z)
              (heap<-all-l (sfix y) z)))
  :enable union)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: better names?

(defrule subset-of-union-left
  (subset x (union x y))
  :enable (pick-a-point
           subset))

(defrule subset-of-union-right
  (subset x (union y x))
  :enable (pick-a-point
           subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule associativity-of-union
  (equal (union (union x y) z)
         (union x y z))
  :enable (double-containment
           pick-a-point
           subset))

(defrule commutativity-of-union
  (equal (union y x)
         (union x y))
  :enable (double-containment
           pick-a-point))
