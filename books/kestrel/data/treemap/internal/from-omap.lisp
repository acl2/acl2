; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)
(include-book "kestrel/data/utilities/omap-defs" :dir :system)
(include-book "kestrel/data/treeset/internal/heap-order-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "heap-defs")
(include-book "keys-defs")
(include-book "in-order-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/data/utilities/omap" :dir :system))
(local (include-book "kestrel/data/treeset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "std/omaps/core" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "keys"))
(local (include-book "in-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; General omap facts. (These may be better placed in an omap utility book.)

(defrulel equal-of-size-and-size-tail
  (equal (equal (omap::size omap)
                (omap::size (omap::tail omap)))
         (omap::emptyp omap))
  :expand ((omap::size omap)))

(defrulel size-of-tail-linear
  (implies (not (omap::emptyp omap))
           (< (omap::size (omap::tail omap))
              (omap::size omap)))
  :rule-classes :linear
  :expand ((omap::size omap)))

(defrulel <<-of-head-and-head-tail-when-not-emptyp
  (implies (not (omap::emptyp (omap::tail omap)))
           (<< (mv-nth 0 (omap::head omap))
               (mv-nth 0 (omap::head (omap::tail omap)))))
  :enable omap::head-tail-order)

(defruledl <<-when-assoc-and-not-assoc-tail
  (implies (and (omap::assoc a omap)
                (not (omap::assoc a (omap::tail omap)))
                (omap::assoc b (omap::tail omap)))
           (<< a b))
  :cases ((equal a b))
  :use ((:instance omap::not-head-key-when-assoc-of-tail
                   (omap::k b)
                   (omap::x omap))
        (:instance omap::head-key-minimal
                   (omap::key b)
                   (omap::map (omap::tail omap)))
        (:instance omap::head-tail-order
                   (omap::x omap))
        (:instance omap::assoc-of-tail-when-not-head
                   (omap::key a)
                   (omap::map omap)))
  :enable data::<<-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Local pick-a-point machinery for <<-all-l. (This may be better placed in
;; bst.lisp, together with a corresponding <<-all-r version.)

(local (include-book "std/util/define-sk" :dir :system))
(local (include-book "kestrel/utilities/polarity" :dir :system))

(local
  (define-sk <<-all-l-sk (tree x)
    :returns (yes/no booleanp :rule-classes :type-prescription)
    (forall (key)
      (non-exec
        (implies (treeset::in key (tree-key-set tree))
                 (<< key x))))))

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
                               (key (tree-element->key (tree->head tree))))))
     :enable (<<-all-l
              <<-all-l-sk-of-tree->left
              <<-all-l-sk-of-tree->right))))

(defruledl <<-all-l-pick-a-point
  (equal (<<-all-l tree x)
         (let ((key (<<-all-l-sk-witness tree x)))
           (implies (treeset::in key (tree-key-set tree))
                    (<< key x))))
  :rule-classes :definition
  :use (<<-all-l-becomes-<<-all-l-sk
        <<-all-l-sk))

(defruledl <<-all-l-pick-a-point-polar
  (implies (syntaxp (acl2::want-to-weaken (<<-all-l tree x)))
           (equal (<<-all-l tree x)
                  (let ((key (<<-all-l-sk-witness tree x)))
                    (implies (treeset::in key (tree-key-set tree))
                             (<< key x)))))
  :rule-classes :definition
  :by <<-all-l-pick-a-point)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A linear-time treap construction from an omap. The entries arrive in
;; ascending key order, so each new entry is the rightmost of the tree so
;; far. tree-from-omap-below consumes entries whose priority lies below the
;; given parent, building the parent's right subtree; when it meets an entry
;; at or above the parent's priority it stops, returning that entry for an
;; enclosing call. Each entry is consed into exactly one node and visited by
;; at most two calls, so the whole construction is O(n).

(define tree-from-omap-below
  ((omap omap::mapp)
   (parent tree-element-p)
   (acc treep))
  :returns (mv (omap$ omap::mapp)
               (acc$ treep))
  (if (omap::emptyp omap)
      (mv nil (tree-fix acc))
    (mv-let (key val)
            (omap::head omap)
      (let ((elem (tree-element$ key val)))
        (if (heap<-with-tree-element elem parent)
            (mv-let (omap$ right)
                    (tree-from-omap-below (omap::tail omap) elem nil)
              (if (mbt (< (omap::size omap$) (omap::size omap)))
                  (tree-from-omap-below omap$ parent (tree-node elem acc right))
                (mv (omap::mfix omap) (tree-fix acc))))
          (mv (omap::mfix omap) (tree-fix acc))))))
  :measure (omap::size omap)
  :hints (("Goal" :expand ((omap::size omap))))
  ;; Verified below, after the size bound.
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-from-omap-below.acc$-type-prescription
  (or (consp (mv-nth 1 (tree-from-omap-below omap parent acc)))
      (equal (mv-nth 1 (tree-from-omap-below omap parent acc)) nil))
  :rule-classes
  ((:type-prescription
    :typed-term (mv-nth 1 (tree-from-omap-below omap parent acc))))
  :use treep-of-tree-from-omap-below.acc$
  :disable treep-of-tree-from-omap-below.acc$)

(defrule tree-from-omap-below-when-tree-element-equiv-congruence
  (implies (tree-element-equiv parent0 parent1)
           (equal (tree-from-omap-below omap parent0 acc)
                  (tree-from-omap-below omap parent1 acc)))
  :rule-classes :congruence
  :induct t
  :enable tree-from-omap-below)

(defrule tree-from-omap-below-when-tree-equiv-congruence
  (implies (tree-equiv acc0 acc1)
           (equal (tree-from-omap-below omap parent acc0)
                  (tree-from-omap-below omap parent acc1)))
  :rule-classes :congruence
  :induct t
  :enable tree-from-omap-below)

;;;;;;;;;;;;;;;;;;;;

(defrule size-of-tree-from-omap-below.omap$-linear
  (<= (omap::size (mv-nth 0 (tree-from-omap-below omap parent acc)))
      (omap::size omap))
  :rule-classes :linear
  :induct t
  :enable tree-from-omap-below)

(verify-guards tree-from-omap-below
  :hints (("Goal" :expand ((omap::size omap)))))

;;;;;;;;;;;;;;;;;;;;

;; The mbt always holds, so the definition unfolds without the guard test.

(defruled tree-from-omap-below-alt-def
  (equal (tree-from-omap-below omap parent acc)
         (if (omap::emptyp omap)
             (mv nil (tree-fix acc))
           (mv-let (key val)
                   (omap::head omap)
             (let ((elem (tree-element$ key val)))
               (if (heap<-with-tree-element elem parent)
                   (mv-let (omap$ right)
                           (tree-from-omap-below (omap::tail omap) elem nil)
                     (tree-from-omap-below omap$ parent
                                           (tree-node elem acc right)))
                 (mv (omap::mfix omap) (tree-fix acc)))))))
  :rule-classes :definition
  :enable tree-from-omap-below
  :expand ((omap::size omap)))

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-tree-from-omap-below.omap$
  (implies (omap::emptyp omap)
           (omap::emptyp
             (mv-nth 0 (tree-from-omap-below omap parent acc))))
  :enable tree-from-omap-below)

;;;;;;;;;;;;;;;;;;;;

;; The remaining omap is drawn from the input.

(defruled assoc-when-assoc-of-tree-from-omap-below.omap$
  (implies (omap::assoc x (mv-nth 0 (tree-from-omap-below omap parent acc)))
           (equal (omap::assoc x (mv-nth 0 (tree-from-omap-below omap
                                                                 parent acc)))
                  (omap::assoc x omap)))
  :induct t
  :enable (tree-from-omap-below
           omap::assoc-when-assoc-tail
           omap::assoc-of-tail-when-assoc-of-tail))

(defrule assoc-when-assoc-of-tree-from-omap-below.omap$-forward-chaining
  (implies (omap::assoc x (mv-nth 0 (tree-from-omap-below omap parent acc)))
           (omap::assoc x omap))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((omap::assoc x (mv-nth 0 (tree-from-omap-below omap parent
                                                                  acc))))))
  :use assoc-when-assoc-of-tree-from-omap-below.omap$)

(defruled not-assoc-of-tree-from-omap-below.omap$-when-not-assoc
  (implies (not (omap::assoc x omap))
           (not (omap::assoc
                  x
                  (mv-nth 0 (tree-from-omap-below omap parent acc)))))
  :use assoc-when-assoc-of-tree-from-omap-below.omap$)

;;;;;;;;;;;;;;;;;;;;

;; The built tree holds the accumulator's keys plus exactly the consumed
;; keys: those of the input not in the remainder.

(defrule in-of-tree-key-set-of-tree-from-omap-below.acc$-when-in
  (implies (treeset::in x (tree-key-set acc))
           (treeset::in
             x
             (tree-key-set (mv-nth 1 (tree-from-omap-below omap parent acc)))))
  :induct t
  :enable tree-from-omap-below)

(defrule in-of-tree-key-set-of-tree-from-omap-below.acc$
  (equal (treeset::in
           x
           (tree-key-set (mv-nth 1 (tree-from-omap-below omap parent acc))))
         (or (treeset::in x (tree-key-set acc))
             (and (omap::assoc x omap)
                  (not (omap::assoc
                         x
                         (mv-nth 0 (tree-from-omap-below omap parent acc))))
                  t)))
  :induct t
  :hints ('(:use (:instance assoc-when-assoc-of-tree-from-omap-below.omap$
                            (x (mv-nth 0 (omap::head omap)))
                            (omap (omap::tail omap))
                            (parent (tree-element$ (mv-nth 0 (omap::head omap))
                                                   (mv-nth 1 (omap::head omap))))
                            (acc nil))))
  :enable ((:i tree-from-omap-below)
           tree-from-omap-below-alt-def))

;;;;;;;;;;;;;;;;;;;;

;; The entries as well: where the built tree binds a consumed key, it binds
;; it to the input's value for that key. The hypothesis keeps the input and
;; the accumulator apart, which every call site satisfies -- the accumulator
;; is always built from keys already consumed.

(defrule assoc-of-tree-omap-of-tree-from-omap-below.acc$
  (implies (not (and (omap::assoc x (tree-omap acc))
                     (omap::assoc x omap)))
           (equal (omap::assoc
                    x
                    (tree-omap (mv-nth 1 (tree-from-omap-below omap parent
                                                               acc))))
                  (if (and (omap::assoc x omap)
                           (not (omap::assoc
                                  x
                                  (mv-nth 0 (tree-from-omap-below omap parent
                                                                  acc)))))
                      (omap::assoc x omap)
                    (omap::assoc x (tree-omap acc)))))
  :induct t
  :hints ('(:use (:instance assoc-when-assoc-of-tree-from-omap-below.omap$
                            (x (mv-nth 0 (omap::head omap)))
                            (omap (omap::tail omap))
                            (parent (tree-element$ (mv-nth 0 (omap::head omap))
                                                   (mv-nth 1 (omap::head omap))))
                            (acc nil))))
  :enable ((:i tree-from-omap-below)
           tree-from-omap-below-alt-def
           tree-omap
           assoc-when-assoc-of-tree-from-omap-below.omap$
           omap::assoc-of-tail-when-assoc-of-tail
           omap::head-key-not-assoc-tail))

;;;;;;;;;;;;;;;;;;;;

;; The remainder's head is at least the input's head, and every consumed
;; key lies strictly below the remainder's head in the total order. This is
;; what makes the construction respect the search-tree invariant: the
;; consumed prefix is all << whatever is left.

(defrule <<-of-head-of-tree-from-omap-below.omap$
  (implies (not (omap::emptyp
                  (mv-nth 0 (tree-from-omap-below omap parent acc))))
           (not (<< (mv-nth 0 (omap::head
                                (mv-nth 0 (tree-from-omap-below omap parent
                                                                acc))))
                    (mv-nth 0 (omap::head omap)))))
  :use ((:instance assoc-when-assoc-of-tree-from-omap-below.omap$
                   (x (mv-nth 0 (omap::head
                                  (mv-nth 0 (tree-from-omap-below omap parent
                                                                  acc))))))
        (:instance omap::head-key-minimal
                   (omap::key (mv-nth 0 (omap::head
                                          (mv-nth 0 (tree-from-omap-below
                                                      omap parent acc)))))
                   (omap::map omap))))

(defruled <<-when-consumed-by-tree-from-omap-below
  (implies (and (omap::assoc a omap)
                (not (omap::assoc
                       a
                       (mv-nth 0 (tree-from-omap-below omap parent acc))))
                (omap::assoc b (mv-nth 0 (tree-from-omap-below omap parent
                                                               acc))))
           (<< a b))
  :induct (tree-from-omap-below omap parent acc)
  :enable ((:i tree-from-omap-below)
           tree-from-omap-below-alt-def
           <<-when-assoc-and-not-assoc-tail))

(defruled <<-of-head-when-consumed-by-tree-from-omap-below
  (implies (and (omap::assoc a omap)
                (not (omap::assoc
                       a
                       (mv-nth 0 (tree-from-omap-below omap parent acc))))
                (not (omap::emptyp
                       (mv-nth 0 (tree-from-omap-below omap parent acc)))))
           (<< a (mv-nth 0 (omap::head
                             (mv-nth 0 (tree-from-omap-below omap parent
                                                             acc))))))
  :use ((:instance <<-when-consumed-by-tree-from-omap-below
                   (b (mv-nth 0 (omap::head
                                  (mv-nth 0 (tree-from-omap-below omap parent
                                                                  acc))))))
        (:instance omap::assoc-of-head
                   (omap::map (mv-nth 0 (tree-from-omap-below omap parent
                                                              acc))))))

;;;;;;;;;;;;;;;;;;;;

;; Anything below the input's head is below the remainder's head too.

(defruled <<-of-head-of-tree-from-omap-below.omap$-of-tail-when-<<-head
  (implies (and (<< x (mv-nth 0 (omap::head omap)))
                (not (omap::emptyp
                       (mv-nth 0 (tree-from-omap-below (omap::tail omap)
                                                       parent acc)))))
           (<< x (mv-nth 0 (omap::head
                             (mv-nth 0 (tree-from-omap-below (omap::tail omap)
                                                             parent acc))))))
  :use ((:instance assoc-when-assoc-of-tree-from-omap-below.omap$
                   (x (mv-nth 0 (omap::head
                                  (mv-nth 0 (tree-from-omap-below
                                              (omap::tail omap) parent acc)))))
                   (omap (omap::tail omap)))
        (:instance <<-when-assoc-and-not-assoc-tail
                   (a (mv-nth 0 (omap::head omap)))
                   (b (mv-nth 0 (omap::head
                                  (mv-nth 0 (tree-from-omap-below
                                              (omap::tail omap) parent
                                              acc))))))
        (:instance omap::assoc-of-head (omap::map omap))
        (:instance omap::assoc-of-head
                   (omap::map (mv-nth 0 (tree-from-omap-below
                                          (omap::tail omap) parent acc))))
        (:instance omap::head-key-not-assoc-tail (omap::map omap)))
  :enable data::<<-rules)

;; The input's head is below the head of what remains of the tail.

(defruled <<-of-head-and-head-of-tree-from-omap-below.omap$-of-tail
  (implies (not (omap::emptyp
                  (mv-nth 0 (tree-from-omap-below (omap::tail omap)
                                                  parent acc))))
           (<< (mv-nth 0 (omap::head omap))
               (mv-nth 0 (omap::head
                           (mv-nth 0 (tree-from-omap-below (omap::tail omap)
                                                           parent acc))))))
  :use ((:instance assoc-when-assoc-of-tree-from-omap-below.omap$
                   (x (mv-nth 0 (omap::head
                                  (mv-nth 0 (tree-from-omap-below
                                              (omap::tail omap) parent acc)))))
                   (omap (omap::tail omap)))
        (:instance <<-when-assoc-and-not-assoc-tail
                   (a (mv-nth 0 (omap::head omap)))
                   (b (mv-nth 0 (omap::head
                                  (mv-nth 0 (tree-from-omap-below
                                              (omap::tail omap) parent
                                              acc))))))
        (:instance omap::assoc-of-head (omap::map omap))
        (:instance omap::assoc-of-head
                   (omap::map (mv-nth 0 (tree-from-omap-below
                                          (omap::tail omap) parent acc))))
        (:instance omap::head-key-not-assoc-tail (omap::map omap))))

(defruled not-equal-of-head-and-head-of-tree-from-omap-below.omap$-of-tail
  (implies (not (omap::emptyp
                  (mv-nth 0 (tree-from-omap-below (omap::tail omap)
                                                  parent acc))))
           (not (equal (mv-nth 0 (omap::head omap))
                       (mv-nth 0 (omap::head
                                   (mv-nth 0 (tree-from-omap-below
                                               (omap::tail omap) parent
                                               acc)))))))
  :use <<-of-head-and-head-of-tree-from-omap-below.omap$-of-tail
  :enable data::<<-rules)

;;;;;;;;;;;;;;;;;;;;

;; The remainder's head is the entry which stopped the consumption loop:
;; its priority is not below the parent's.

(defrule not-heap<-of-head-of-tree-from-omap-below.omap$
  (implies (not (omap::emptyp
                  (mv-nth 0 (tree-from-omap-below omap parent acc))))
           (not (heap< (mv-nth 0 (omap::head
                                   (mv-nth 0 (tree-from-omap-below omap parent
                                                                   acc))))
                       (tree-element->key parent))))
  :induct t
  :enable ((:i tree-from-omap-below)
           tree-from-omap-below-alt-def
           heap<-rules))

;; Variant stated in the normalized form which appears in induction goals,
;; where the rule above cannot match syntactically.

(defruled not-heap<-of-head-of-tree-from-omap-below.omap$-alt
  (implies (not (omap::emptyp
                  (mv-nth 0 (tree-from-omap-below omap (tree-element nil x v)
                                                  acc))))
           (not (heap< (mv-nth 0 (omap::head
                                   (mv-nth 0 (tree-from-omap-below
                                               omap (tree-element nil x v)
                                               acc))))
                       x)))
  :use (:instance not-heap<-of-head-of-tree-from-omap-below.omap$
                  (parent (tree-element nil x v)))
  :disable not-heap<-of-head-of-tree-from-omap-below.omap$)

;; Positive form, for the driver: each new root's priority lies below that
;; of the entry which stopped its consumption loop.

(defruled heap<-of-head-and-head-of-tree-from-omap-below.omap$-of-tail
  (implies (not (omap::emptyp
                  (mv-nth 0 (tree-from-omap-below
                              (omap::tail omap)
                              (tree-element nil
                                            (mv-nth 0 (omap::head omap))
                                            (mv-nth 1 (omap::head omap)))
                              acc))))
           (heap< (mv-nth 0 (omap::head omap))
                  (mv-nth 0 (omap::head
                              (mv-nth 0 (tree-from-omap-below
                                          (omap::tail omap)
                                          (tree-element
                                            nil
                                            (mv-nth 0 (omap::head omap))
                                            (mv-nth 1 (omap::head omap)))
                                          acc))))))
  :use ((:instance not-heap<-of-head-of-tree-from-omap-below.omap$-alt
                   (omap (omap::tail omap))
                   (x (mv-nth 0 (omap::head omap)))
                   (v (mv-nth 1 (omap::head omap))))
        (:instance
          not-equal-of-head-and-head-of-tree-from-omap-below.omap$-of-tail
          (parent (tree-element nil
                                (mv-nth 0 (omap::head omap))
                                (mv-nth 1 (omap::head omap))))))
  :enable (heap<-rules
           treeset::heap<-expensive-rules))

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
;; to come; each new node's right subtree holds only consumed keys, which
;; the lemma above places below the next remaining key.

(defrule <<-all-r-of-tree-from-omap-below.acc$
  (implies (and (or (omap::emptyp omap)
                    (<< x (mv-nth 0 (omap::head omap))))
                (<<-all-r x acc))
           (<<-all-r x (mv-nth 1 (tree-from-omap-below omap parent acc))))
  :induct t
  :enable ((:i tree-from-omap-below)
           tree-from-omap-below-alt-def
           <<-of-head-of-tree-from-omap-below.omap$-of-tail-when-<<-head
           data::<<-rules))

(defrule <<-all-l-of-tree-from-omap-below.acc$
  (implies (and (<<-all-l acc (mv-nth 0 (omap::head
                                          (mv-nth 0
                                                  (tree-from-omap-below
                                                    omap parent acc)))))
                (not (omap::emptyp
                       (mv-nth 0 (tree-from-omap-below omap parent acc)))))
           (<<-all-l (mv-nth 1 (tree-from-omap-below omap parent acc))
                     (mv-nth 0 (omap::head
                                 (mv-nth 0 (tree-from-omap-below omap parent
                                                                 acc))))))
  :enable (<<-all-l-pick-a-point-polar
           <<-of-head-when-consumed-by-tree-from-omap-below
           data::<<-rules))

(defrule bstp-of-tree-from-omap-below.acc$
  (implies (and (bstp acc)
                (<<-all-r (tree-element->key parent) acc)
                (or (omap::emptyp omap)
                    (and (<<-all-l acc (mv-nth 0 (omap::head omap)))
                         (<< (tree-element->key parent)
                             (mv-nth 0 (omap::head omap))))))
           (bstp (mv-nth 1 (tree-from-omap-below omap parent acc))))
  :induct t
  :enable ((:i tree-from-omap-below)
           tree-from-omap-below-alt-def
           <<-of-head-and-head-of-tree-from-omap-below.omap$-of-tail
           <<-all-l-weaken-alt
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

;; The heap invariant. Everything consumed below the parent carries a lower
;; priority than the parent, by construction. The bound is generalized to
;; any x at or above the parent so the rule can match goals where the bound
;; is not written as (tree-element->key parent).

(defrule heap<-all-l-of-tree-from-omap-below.acc$
  (implies (and (heap<-all-l acc x)
                (not (heap< x (tree-element->key parent))))
           (heap<-all-l (mv-nth 1 (tree-from-omap-below omap parent acc)) x))
  :induct t
  :enable (tree-from-omap-below
           heap<-all-l-weaken
           heap<-rules
           treeset::heap<-expensive-rules))

;; Note the invariant hypothesis: the accumulator must also lie below the
;; next entry to be consumed, since that entry takes the accumulator as its
;; left subtree.

(defrule heapp-of-tree-from-omap-below.acc$
  (implies (and (heapp acc)
                (heap<-all-l acc (tree-element->key parent))
                (or (omap::emptyp omap)
                    (heap<-all-l acc (mv-nth 0 (omap::head omap)))))
           (heapp (mv-nth 1 (tree-from-omap-below omap parent acc))))
  :induct t
  :enable ((:i tree-from-omap-below)
           tree-from-omap-below-alt-def
           heap<-all-l-weaken
           not-equal-of-head-and-head-of-tree-from-omap-below.omap$-of-tail
           not-heap<-of-head-of-tree-from-omap-below.omap$-alt
           heap<-rules
           treeset::heap<-expensive-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The driver. Each iteration takes the least remaining entry as a new
;; root: its right subtree is everything below its priority, and the tree so
;; far — all smaller in the total order, all lower in priority — hangs to
;; its left.

(define tree-from-omap-acc
  ((omap omap::mapp)
   (acc treep))
  :returns (tree treep)
  (if (omap::emptyp omap)
      (tree-fix acc)
    (mv-let (key val)
            (omap::head omap)
      (let ((elem (tree-element$ key val)))
        (mv-let (omap$ right)
                (tree-from-omap-below (omap::tail omap) elem nil)
          (tree-from-omap-acc omap$ (tree-node elem acc right))))))
  :measure (omap::size omap)
  :hints (("Goal" :expand ((omap::size omap)))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-from-omap-acc-type-prescription
  (or (consp (tree-from-omap-acc omap acc))
      (equal (tree-from-omap-acc omap acc) nil))
  :rule-classes
  ((:type-prescription :typed-term (tree-from-omap-acc omap acc)))
  :use treep-of-tree-from-omap-acc
  :disable treep-of-tree-from-omap-acc)

(defrule tree-from-omap-acc-when-tree-equiv-congruence
  (implies (tree-equiv acc0 acc1)
           (equal (tree-from-omap-acc omap acc0)
                  (tree-from-omap-acc omap acc1)))
  :rule-classes :congruence
  :induct t
  :enable tree-from-omap-acc)

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree-key-set-of-tree-from-omap-acc
  (equal (treeset::in x (tree-key-set (tree-from-omap-acc omap acc)))
         (or (treeset::in x (tree-key-set acc))
             (and (omap::assoc x omap) t)))
  :induct t
  :enable (tree-from-omap-acc
           not-assoc-of-tree-from-omap-below.omap$-when-not-assoc))

(defrule assoc-of-tree-omap-of-tree-from-omap-acc
  (implies (not (and (omap::assoc x (tree-omap acc))
                     (omap::assoc x omap)))
           (equal (omap::assoc x (tree-omap (tree-from-omap-acc omap acc)))
                  (if (omap::assoc x omap)
                      (omap::assoc x omap)
                    (omap::assoc x (tree-omap acc)))))
  :hints (("Goal"
           :induct (tree-from-omap-acc omap acc)
           :in-theory (enable tree-from-omap-acc
                              tree-omap
                              not-assoc-of-tree-from-omap-below.omap$-when-not-assoc
                              assoc-when-assoc-of-tree-from-omap-below.omap$
                              omap::assoc-of-tail-when-assoc-of-tail
                              omap::head-key-not-assoc-tail))
          ;; The head's key cannot survive into the remainder -- it is not in
          ;; the tail the consumption ran on -- but that instance must be
          ;; named: the fact sits under an mv-nth the rewriter has already
          ;; taken apart.
          (and stable-under-simplificationp
               '(:use (:instance
                        not-assoc-of-tree-from-omap-below.omap$-when-not-assoc
                        (x (mv-nth 0 (omap::head omap)))
                        (omap (omap::tail omap))
                        (parent (tree-element nil
                                              (mv-nth 0 (omap::head omap))
                                              (mv-nth 1 (omap::head omap))))
                        (acc nil))))))

(defrule bstp-of-tree-from-omap-acc
  (implies (and (bstp acc)
                (or (omap::emptyp omap)
                    (<<-all-l acc (mv-nth 0 (omap::head omap)))))
           (bstp (tree-from-omap-acc omap acc)))
  :induct t
  :enable (tree-from-omap-acc
           <<-of-head-and-head-of-tree-from-omap-below.omap$-of-tail
           <<-all-l-weaken-alt
           data::<<-rules))

(defrule heapp-of-tree-from-omap-acc
  (implies (and (heapp acc)
                (or (omap::emptyp omap)
                    (heap<-all-l acc (mv-nth 0 (omap::head omap)))))
           (heapp (tree-from-omap-acc omap acc)))
  :induct t
  :enable (tree-from-omap-acc
           heap<-all-l-weaken-alt
           heap<-of-head-and-head-of-tree-from-omap-below.omap$-of-tail
           not-heap<-of-head-of-tree-from-omap-below.omap$-alt
           heap<-rules
           treeset::heap<-expensive-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-from-omap ((omap omap::mapp))
  :returns (tree treep)
  :parents (implementation)
  :short "Build a treap holding an omap's entries, in linear time."
  (tree-from-omap-acc omap nil)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-from-omap-type-prescription
  (or (consp (tree-from-omap omap))
      (equal (tree-from-omap omap) nil))
  :rule-classes ((:type-prescription :typed-term (tree-from-omap omap)))
  :use treep-of-tree-from-omap
  :disable treep-of-tree-from-omap)

(defrule in-of-tree-key-set-of-tree-from-omap
  (equal (treeset::in x (tree-key-set (tree-from-omap omap)))
         (and (omap::assoc x omap) t))
  :enable tree-from-omap)

(defrule assoc-of-tree-omap-of-tree-from-omap
  (equal (omap::assoc x (tree-omap (tree-from-omap omap)))
         (omap::assoc x omap))
  :enable tree-from-omap)

(defrule bstp-of-tree-from-omap
  (bstp (tree-from-omap omap))
  :enable tree-from-omap)

(defrule heapp-of-tree-from-omap
  (heapp (tree-from-omap omap))
  :enable tree-from-omap)
