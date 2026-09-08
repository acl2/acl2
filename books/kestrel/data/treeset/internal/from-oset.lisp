; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/utilities/oset-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "heap-defs")
(include-book "heap-order-defs")
(include-book "in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/utilities/oset" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "heap-order"))
(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; General oset facts. (These may be better placed in an oset utility book.)

(defrulel equal-of-cardinality-and-cardinality-tail
  (equal (equal (set::cardinality oset)
                (set::cardinality (set::tail oset)))
         (set::emptyp oset))
  :expand ((set::cardinality oset)))

(defrulel <<-of-head-and-head-tail-when-not-emptyp
  (implies (not (set::emptyp (set::tail oset)))
           (<< (set::head oset)
               (set::head (set::tail oset))))
  :enable (set::head
           set::tail
           set::emptyp
           set::setp
           set::sfix))

(defruledl <<-when-in-and-not-in-tail
  (implies (and (set::in a oset)
                (not (set::in a (set::tail oset)))
                (set::in b (set::tail oset)))
           (<< a b))
  :cases ((equal a b))
  :use ((:instance set::in-tail-or-head (acl2::a a) (acl2::x oset))
        (:instance set::head-minimal-2 (acl2::a b) (acl2::x oset)))
  :enable (data::<<-rules
           set::in-tail))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Local pick-a-point machinery for <<-all-l. (This may be better placed in
;; bst.lisp, together with a corresponding <<-all-r version.)

(local (include-book "std/util/define-sk" :dir :system))
(local (include-book "kestrel/utilities/polarity" :dir :system))

(local
  (define-sk <<-all-l-sk (tree x)
    :returns (yes/no booleanp :rule-classes :type-prescription)
    (forall (elem)
      (non-exec
        (implies (tree-in elem tree)
                 (<< elem x))))))

(local (in-theory (disable (:t <<-all-l-sk))))

(defruledl <<-all-l-sk-of-tree->left
  (implies (<<-all-l-sk tree x)
           (<<-all-l-sk (tree->left tree) x))
  :enable <<-all-l-sk-necc
  :expand (<<-all-l-sk (tree->left tree) x))

(defruledl <<-all-l-sk-of-tree->right
  (implies (<<-all-l-sk tree x)
           (<<-all-l-sk (tree->right tree) x))
  :enable <<-all-l-sk-necc
  :expand (<<-all-l-sk (tree->right tree) x))

(defruledl <<-all-l-becomes-<<-all-l-sk
  (equal (<<-all-l tree x)
         (<<-all-l-sk tree x))
  :rule-classes :definition
  :use (<<-all-l-sk-when-<<-all-l
        <<-all-l-when-<<-all-l-sk)

  :prep-lemmas
  ((defruled <<-all-l-sk-when-<<-all-l
     (implies (<<-all-l tree x)
              (<<-all-l-sk tree x))
     :enable <<-all-l-sk)

   (defruled <<-all-l-when-<<-all-l-sk
     (implies (<<-all-l-sk tree x)
              (<<-all-l tree x))
     :induct t
     :hints ('(:use (:instance <<-all-l-sk-necc
                               (elem (tree-element->val (tree->head tree))))))
     :enable (<<-all-l
              <<-all-l-sk-of-tree->left
              <<-all-l-sk-of-tree->right))))

(defruledl <<-all-l-pick-a-point
  (equal (<<-all-l tree x)
         (let ((elem (<<-all-l-sk-witness tree x)))
           (implies (tree-in elem tree)
                    (<< elem x))))
  :rule-classes :definition
  :use (<<-all-l-becomes-<<-all-l-sk
        <<-all-l-sk))

(defruledl <<-all-l-pick-a-point-polar
  (implies (syntaxp (acl2::want-to-weaken (<<-all-l tree x)))
           (equal (<<-all-l tree x)
                  (let ((elem (<<-all-l-sk-witness tree x)))
                    (implies (tree-in elem tree)
                             (<< elem x)))))
  :rule-classes :definition
  :by <<-all-l-pick-a-point)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A linear-time treap construction from an ordered set. The elements arrive
;; in ascending order, so each new element is the rightmost of the tree so
;; far. tree-from-oset-below consumes elements whose priority lies below the
;; given parent, building the parent's right subtree; when it meets an
;; element at or above the parent's priority it stops, returning that element
;; for an enclosing call. Each element is consed into exactly one node and
;; visited by at most two calls, so the whole construction is O(n).

(define tree-from-oset-below
  ((oset set::setp)
   (parent tree-element-p)
   (acc treep))
  :returns (mv (oset$ set::setp)
               (acc$ treep))
  (if (set::emptyp oset)
      (mv nil (tree-fix acc))
    (let ((elem (tree-element$ (set::head oset))))
      (if (heap<-with-tree-element elem parent)
          (mv-let (oset$ right)
                  (tree-from-oset-below (set::tail oset) elem nil)
            (if (mbt (< (set::cardinality oset$) (set::cardinality oset)))
                (tree-from-oset-below oset$ parent (tree-node elem acc right))
              (mv oset (tree-fix acc))))
        (mv oset (tree-fix acc)))))
  :measure (set::cardinality oset)
  ;; Verified below, after the cardinality bound.
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-from-oset-below.oset$-type-prescription
  (or (consp (mv-nth 0 (tree-from-oset-below oset parent acc)))
      (equal (mv-nth 0 (tree-from-oset-below oset parent acc)) nil))
  :rule-classes
  ((:type-prescription
    :typed-term (mv-nth 0 (tree-from-oset-below oset parent acc))))
  :use setp-of-tree-from-oset-below.oset$
  :disable setp-of-tree-from-oset-below.oset$)

(defrule tree-from-oset-below.acc$-type-prescription
  (or (consp (mv-nth 1 (tree-from-oset-below oset parent acc)))
      (equal (mv-nth 1 (tree-from-oset-below oset parent acc)) nil))
  :rule-classes
  ((:type-prescription
    :typed-term (mv-nth 1 (tree-from-oset-below oset parent acc))))
  :use treep-of-tree-from-oset-below.acc$
  :disable treep-of-tree-from-oset-below.acc$)

(defrule tree-from-oset-below-when-tree-element-equiv-congruence
  (implies (tree-element-equiv parent0 parent1)
           (equal (tree-from-oset-below oset parent0 acc)
                  (tree-from-oset-below oset parent1 acc)))
  :rule-classes :congruence
  :induct t
  :enable tree-from-oset-below)

(defrule tree-from-oset-below-when-tree-equiv-congruence
  (implies (tree-equiv acc0 acc1)
           (equal (tree-from-oset-below oset parent acc0)
                  (tree-from-oset-below oset parent acc1)))
  :rule-classes :congruence
  :induct t
  :enable tree-from-oset-below)

;;;;;;;;;;;;;;;;;;;;

(defrule cardinality-of-tree-from-oset-below.oset$-linear
  (<= (set::cardinality (mv-nth 0 (tree-from-oset-below oset parent acc)))
      (set::cardinality oset))
  :rule-classes :linear
  :induct t
  :enable tree-from-oset-below)

(verify-guards tree-from-oset-below)

;;;;;;;;;;;;;;;;;;;;

;; The mbt always holds, so the definition unfolds without the guard test.

(defruled tree-from-oset-below-alt-def
  (equal (tree-from-oset-below oset parent acc)
         (if (set::emptyp oset)
             (mv nil (tree-fix acc))
           (let ((elem (tree-element$ (set::head oset))))
             (if (heap<-with-tree-element elem parent)
                 (mv-let (oset$ right)
                         (tree-from-oset-below (set::tail oset) elem nil)
                   (tree-from-oset-below oset$ parent
                                         (tree-node elem acc right)))
               (mv oset (tree-fix acc))))))
  :rule-classes :definition
  :enable tree-from-oset-below)

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-tree-from-oset-below.oset$
  (implies (set::emptyp oset)
           (set::emptyp
             (mv-nth 0 (tree-from-oset-below oset parent acc))))
  :enable tree-from-oset-below)

;;;;;;;;;;;;;;;;;;;;

;; The remaining oset is drawn from the input.

(defruled in-when-in-of-tree-from-oset-below.oset$
  (implies (set::in x (mv-nth 0 (tree-from-oset-below oset parent acc)))
           (set::in x oset))
  :induct t
  :enable tree-from-oset-below)

(defrule in-when-in-of-tree-from-oset-below.oset$-forward-chaining
  (implies (set::in x (mv-nth 0 (tree-from-oset-below oset parent acc)))
           (set::in x oset))
  :rule-classes :forward-chaining
  :by in-when-in-of-tree-from-oset-below.oset$)

(defruled not-in-of-tree-from-oset-below.oset$-when-not-in
  (implies (not (set::in x oset))
           (not (set::in
                  x
                  (mv-nth 0 (tree-from-oset-below oset parent acc)))))
  :use in-when-in-of-tree-from-oset-below.oset$)

(defrule subset-of-tree-from-oset-below.oset$-and-oset
  (set::subset (mv-nth 0 (tree-from-oset-below oset parent acc))
               oset)
  :enable set::expensive-rules)

;;;;;;;;;;;;;;;;;;;;

;; The built tree holds the accumulator's elements plus exactly the consumed
;; elements: those of the input not in the remainder.

(defrule tree-in-of-tree-from-oset-below.acc$-when-tree-in
  (implies (tree-in x acc)
           (tree-in x (mv-nth 1 (tree-from-oset-below oset parent acc))))
  :induct t
  :enable tree-from-oset-below)

(defrule tree-in-of-tree-from-oset-below.acc$
  (equal (tree-in val (mv-nth 1 (tree-from-oset-below oset parent acc)))
         (or (tree-in val acc)
             (and (set::in val oset)
                  (not (set::in
                         val
                         (mv-nth 0 (tree-from-oset-below oset parent acc)))))))
  :induct t
  :hints ('(:use (:instance in-when-in-of-tree-from-oset-below.oset$
                            (x (set::head oset))
                            (oset (set::tail oset))
                            (parent (tree-element nil (set::head oset)))
                            (acc nil))))
  :enable ((:i tree-from-oset-below)
           tree-from-oset-below-alt-def))

;;;;;;;;;;;;;;;;;;;;

;; The remainder's head is at least the input's head, and every consumed
;; element lies strictly below the remainder's head in the total order. This
;; is what makes the construction respect the search-tree invariant: the
;; consumed prefix is all << whatever is left.

(defrule <<-of-head-of-tree-from-oset-below.oset$
  (implies (not (set::emptyp
                  (mv-nth 0 (tree-from-oset-below oset parent acc))))
           (not (<< (set::head
                      (mv-nth 0 (tree-from-oset-below oset parent acc)))
                    (set::head oset))))
  :use (:instance in-when-in-of-tree-from-oset-below.oset$
                  (x (set::head
                       (mv-nth 0 (tree-from-oset-below oset parent acc))))
                  (oset oset))
  :enable set::head-minimal-2)

(defruled <<-when-consumed-by-tree-from-oset-below
  (implies (and (set::in a oset)
                (not (set::in
                       a
                       (mv-nth 0 (tree-from-oset-below oset parent acc))))
                (set::in b (mv-nth 0 (tree-from-oset-below oset parent acc))))
           (<< a b))
  :induct (tree-from-oset-below oset parent acc)
  :enable ((:i tree-from-oset-below)
           tree-from-oset-below-alt-def
           <<-when-in-and-not-in-tail))

(defruled <<-of-head-when-consumed-by-tree-from-oset-below
  (implies (and (set::in a oset)
                (not (set::in
                       a
                       (mv-nth 0 (tree-from-oset-below oset parent acc))))
                (not (set::emptyp
                       (mv-nth 0 (tree-from-oset-below oset parent acc)))))
           (<< a (set::head
                   (mv-nth 0 (tree-from-oset-below oset parent acc)))))
  :use (:instance <<-when-consumed-by-tree-from-oset-below
                  (b (set::head
                       (mv-nth 0 (tree-from-oset-below oset parent acc))))))

;;;;;;;;;;;;;;;;;;;;

;; Anything below the input's head is below the remainder's head too.

(defruled <<-of-head-of-tree-from-oset-below.oset$-of-tail-when-<<-head
  (implies (and (<< x (set::head oset))
                (not (set::emptyp
                       (mv-nth 0 (tree-from-oset-below (set::tail oset)
                                                       parent acc)))))
           (<< x (set::head
                   (mv-nth 0 (tree-from-oset-below (set::tail oset)
                                                   parent acc)))))
  :use ((:instance in-when-in-of-tree-from-oset-below.oset$
                   (x (set::head
                        (mv-nth 0 (tree-from-oset-below (set::tail oset)
                                                        parent acc))))
                   (oset (set::tail oset)))
        (:instance <<-when-in-and-not-in-tail
                   (a (set::head oset))
                   (b (set::head
                        (mv-nth 0 (tree-from-oset-below (set::tail oset)
                                                        parent acc))))))
  :enable (data::<<-rules
           set::in-head
           set::tail-when-emptyp))

;; The input's head is below the head of what remains of the tail.

(defruled <<-of-head-and-head-of-tree-from-oset-below.oset$-of-tail
  (implies (not (set::emptyp
                  (mv-nth 0 (tree-from-oset-below (set::tail oset)
                                                  parent acc))))
           (<< (set::head oset)
               (set::head
                 (mv-nth 0 (tree-from-oset-below (set::tail oset)
                                                 parent acc)))))
  :use ((:instance in-when-in-of-tree-from-oset-below.oset$
                   (x (set::head
                        (mv-nth 0 (tree-from-oset-below (set::tail oset)
                                                        parent acc))))
                   (oset (set::tail oset)))
        (:instance <<-when-in-and-not-in-tail
                   (a (set::head oset))
                   (b (set::head
                        (mv-nth 0 (tree-from-oset-below (set::tail oset)
                                                        parent acc))))))
  :enable (set::in-head
           set::tail-when-emptyp))

(defruled not-equal-of-head-and-head-of-tree-from-oset-below.oset$-of-tail
  (implies (not (set::emptyp
                  (mv-nth 0 (tree-from-oset-below (set::tail oset)
                                                  parent acc))))
           (not (equal (set::head oset)
                       (set::head
                         (mv-nth 0 (tree-from-oset-below (set::tail oset)
                                                         parent acc))))))
  :use <<-of-head-and-head-of-tree-from-oset-below.oset$-of-tail
  :enable data::<<-rules)

;;;;;;;;;;;;;;;;;;;;

;; The remainder's head is the element which stopped the consumption loop:
;; its priority is not below the parent's.

(defrule not-heap<-of-head-of-tree-from-oset-below.oset$
  (implies (not (set::emptyp
                  (mv-nth 0 (tree-from-oset-below oset parent acc))))
           (not (heap< (set::head
                         (mv-nth 0 (tree-from-oset-below oset parent acc)))
                       (tree-element->val parent))))
  :induct t
  :enable ((:i tree-from-oset-below)
           tree-from-oset-below-alt-def
           heap<-rules))

;; Variant stated in the normalized (tree-element nil x) form which appears
;; in induction goals, where the rule above cannot match syntactically.

(defruled not-heap<-of-head-of-tree-from-oset-below.oset$-alt
  (implies (not (set::emptyp
                  (mv-nth 0 (tree-from-oset-below oset (tree-element nil x)
                                                  acc))))
           (not (heap< (set::head
                         (mv-nth 0 (tree-from-oset-below
                                     oset (tree-element nil x) acc)))
                       x)))
  :use (:instance not-heap<-of-head-of-tree-from-oset-below.oset$
                  (parent (tree-element nil x)))
  :disable not-heap<-of-head-of-tree-from-oset-below.oset$)

;; Positive form, for the driver: each new root's priority lies below that
;; of the element which stopped its consumption loop.

(defruled heap<-of-head-and-head-of-tree-from-oset-below.oset$-of-tail
  (implies (not (set::emptyp
                  (mv-nth 0 (tree-from-oset-below
                              (set::tail oset)
                              (tree-element nil (set::head oset))
                              acc))))
           (heap< (set::head oset)
                  (set::head
                    (mv-nth 0 (tree-from-oset-below
                                (set::tail oset)
                                (tree-element nil (set::head oset))
                                acc)))))
  :use ((:instance not-heap<-of-head-of-tree-from-oset-below.oset$-alt
                   (oset (set::tail oset))
                   (x (set::head oset)))
        (:instance
          not-equal-of-head-and-head-of-tree-from-oset-below.oset$-of-tail
          (parent (tree-element nil (set::head oset)))))
  :enable (heap<-rules
           heap<-expensive-rules))

;; Like heap<-all-l-weaken, but the hypothesis order binds the free variable
;; by matching known heap<-all-l facts rather than known heap< facts. (This
;; may be better placed in heap.lisp, mirroring <<-all-l-weaken-alt in
;; bst.lisp.)

(defruledl heap<-all-l-weaken-alt
  (implies (and (heap<-all-l tree y)
                (heap< y x))
           (heap<-all-l tree x))
  :by heap<-all-l-weaken)

;;;;;;;;;;;;;;;;;;;;

;; The search-tree invariant. The accumulator sits left of everything still
;; to come; each new node's right subtree holds only consumed elements, which
;; the lemma above places below the next remaining element.

(defrule <<-all-r-of-tree-from-oset-below.acc$
  (implies (and (or (set::emptyp oset)
                    (<< x (set::head oset)))
                (<<-all-r x acc))
           (<<-all-r x (mv-nth 1 (tree-from-oset-below oset parent acc))))
  :induct t
  :enable ((:i tree-from-oset-below)
           tree-from-oset-below-alt-def
           <<-of-head-of-tree-from-oset-below.oset$-of-tail-when-<<-head
           set::head-minimal-2
           data::<<-rules))

(defrule <<-all-l-of-tree-from-oset-below.acc$
  (implies (and (<<-all-l acc (set::head
                                (mv-nth 0
                                        (tree-from-oset-below oset parent
                                                              acc))))
                (not (set::emptyp
                       (mv-nth 0 (tree-from-oset-below oset parent acc)))))
           (<<-all-l (mv-nth 1 (tree-from-oset-below oset parent acc))
                     (set::head
                       (mv-nth 0 (tree-from-oset-below oset parent acc)))))
  :enable (<<-all-l-pick-a-point-polar
           <<-of-head-when-consumed-by-tree-from-oset-below
           data::<<-rules))

(defrule bstp-of-tree-from-oset-below.acc$
  (implies (and (bstp acc)
                (<<-all-r (tree-element->val parent) acc)
                (or (set::emptyp oset)
                    (and (<<-all-l acc (set::head oset))
                         (<< (tree-element->val parent) (set::head oset)))))
           (bstp (mv-nth 1 (tree-from-oset-below oset parent acc))))
  :induct t
  :enable ((:i tree-from-oset-below)
           tree-from-oset-below-alt-def
           <<-of-head-and-head-of-tree-from-oset-below.oset$-of-tail
           <<-all-l-weaken-alt
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

;; The heap invariant. Everything consumed below the parent carries a lower
;; priority than the parent, by construction. The bound is generalized to
;; any x at or above the parent so the rule can match goals where the bound
;; is not written as (tree-element->val parent).

(defrule heap<-all-l-of-tree-from-oset-below.acc$
  (implies (and (heap<-all-l acc x)
                (not (heap< x (tree-element->val parent))))
           (heap<-all-l (mv-nth 1 (tree-from-oset-below oset parent acc)) x))
  :induct t
  :enable (tree-from-oset-below
           heap<-all-l-weaken
           heap<-rules
           heap<-expensive-rules))

;; Note the invariant hypothesis: the accumulator must also lie below the
;; next element to be consumed, since that element takes the accumulator as
;; its left subtree.

(defrule heapp-of-tree-from-oset-below.acc$
  (implies (and (heapp acc)
                (heap<-all-l acc (tree-element->val parent))
                (or (set::emptyp oset)
                    (heap<-all-l acc (set::head oset))))
           (heapp (mv-nth 1 (tree-from-oset-below oset parent acc))))
  :induct t
  :enable ((:i tree-from-oset-below)
           tree-from-oset-below-alt-def
           heap<-all-l-weaken
           not-equal-of-head-and-head-of-tree-from-oset-below.oset$-of-tail
           not-heap<-of-head-of-tree-from-oset-below.oset$-alt
           heap<-rules
           heap<-expensive-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The driver. Each iteration takes the least remaining element as a new
;; root: its right subtree is everything below its priority, and the tree so
;; far — all smaller in the total order, all lower in priority — hangs to
;; its left.

(define tree-from-oset-acc
  ((oset set::setp)
   (acc treep))
  :returns (tree treep)
  (if (set::emptyp oset)
      (tree-fix acc)
    (let ((elem (tree-element$ (set::head oset))))
      (mv-let (oset$ right)
              (tree-from-oset-below (set::tail oset) elem nil)
        (tree-from-oset-acc oset$ (tree-node elem acc right)))))
  :measure (set::cardinality oset))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-from-oset-acc-type-prescription
  (or (consp (tree-from-oset-acc oset acc))
      (equal (tree-from-oset-acc oset acc) nil))
  :rule-classes
  ((:type-prescription :typed-term (tree-from-oset-acc oset acc)))
  :use treep-of-tree-from-oset-acc
  :disable treep-of-tree-from-oset-acc)

(defrule tree-from-oset-acc-when-tree-equiv-congruence
  (implies (tree-equiv acc0 acc1)
           (equal (tree-from-oset-acc oset acc0)
                  (tree-from-oset-acc oset acc1)))
  :rule-classes :congruence
  :induct t
  :enable tree-from-oset-acc)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-tree-from-oset-acc
  (equal (tree-in x (tree-from-oset-acc oset acc))
         (or (tree-in x acc)
             (set::in x oset)))
  :induct t
  :enable (tree-from-oset-acc
           not-in-of-tree-from-oset-below.oset$-when-not-in))

(defrule bstp-of-tree-from-oset-acc
  (implies (and (bstp acc)
                (or (set::emptyp oset)
                    (<<-all-l acc (set::head oset))))
           (bstp (tree-from-oset-acc oset acc)))
  :induct t
  :enable (tree-from-oset-acc
           <<-of-head-and-head-of-tree-from-oset-below.oset$-of-tail
           <<-all-l-weaken-alt
           data::<<-rules))

(defrule heapp-of-tree-from-oset-acc
  (implies (and (heapp acc)
                (or (set::emptyp oset)
                    (heap<-all-l acc (set::head oset))))
           (heapp (tree-from-oset-acc oset acc)))
  :induct t
  :enable (tree-from-oset-acc
           heap<-all-l-weaken-alt
           heap<-of-head-and-head-of-tree-from-oset-below.oset$-of-tail
           not-heap<-of-head-of-tree-from-oset-below.oset$-alt
           heap<-rules
           heap<-expensive-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-from-oset ((oset set::setp))
  :returns (tree treep)
  :parents (implementation)
  :short "Build a treap holding an oset's elements, in linear time."
  (tree-from-oset-acc oset nil)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-from-oset-type-prescription
  (or (consp (tree-from-oset oset))
      (equal (tree-from-oset oset) nil))
  :rule-classes ((:type-prescription :typed-term (tree-from-oset oset)))
  :use treep-of-tree-from-oset
  :disable treep-of-tree-from-oset)

(defrule tree-in-of-tree-from-oset
  (equal (tree-in x (tree-from-oset oset))
         (set::in x oset))
  :enable tree-from-oset)

(defrule bstp-of-tree-from-oset
  (bstp (tree-from-oset oset))
  :enable tree-from-oset)

(defrule heapp-of-tree-from-oset
  (heapp (tree-from-oset oset))
  :enable tree-from-oset)
