; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "heap-defs")
(include-book "in-defs")
(include-book "min-max-defs")
(include-book "subset-defs")
(include-book "insert-defs")
(include-book "delete-defs")
(include-book "union-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system)) ; Unnecessary?
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "../hash"))
(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "in"))
(local (include-book "subset"))
(local (include-book "antisymmetry"))
(local (include-book "insert"))
(local (include-book "delete"))
(local (include-book "union"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An iterator is a list of nonempty sets
;; The interpretation is that each set in the list represents the head,
;; followed by the iterator-expansion of the right child, and then the rest of
;; the iterator. The left children are irrelevant.

(define tree-iter-p (x)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (if (consp x)
      (and (mbe :logic (and (treep (first x))
                            (not (tree-empty-p (first x))))
                :exec (and (consp (first x))
                           (tagged-element-p (car (first x)))
                           (consp (cdr (first x)))
                           (treep (cadr (first x)))
                           (treep (cddr (first x)))))
           (tree-iter-p (rest x)))
    (null x))
  :guard-hints (("Goal" :in-theory (enable treep
                                           tree-empty-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter-p)))

(defruled true-listp-when-tree-iter-p
  (implies (tree-iter-p x)
           (true-listp x))
  :induct t
  :enable tree-iter-p)

(defrule tree-iter-p-compound-recognizer
  (implies (tree-iter-p x)
           (true-listp x))
  :rule-classes :compound-recognizer
  :by true-listp-when-tree-iter-p)

(defruled tree-listp-when-tree-iter-p
  (implies (tree-iter-p x)
           (tree-listp x))
  :induct t
  :enable (tree-iter-p
           tree-listp))

(defrule tree-listp-when-tree-iter-p-forward-chaining
  (implies (tree-iter-p x)
           (tree-listp x))
  :rule-classes :forward-chaining
  :by tree-listp-when-tree-iter-p)

(defruled treep-of-car-when-tree-iter-p
  (implies (tree-iter-p iter)
           (treep (car iter)))
  :enable tree-iter-p)

(defrule treep-of-car-when-tree-iter-p-cheap
  (implies (tree-iter-p iter)
           (treep (car iter)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by treep-of-car-when-tree-iter-p)

(defruled tree-empty-p-of-car-when-tree-iter-p
  (implies (tree-iter-p iter)
           (equal (tree-empty-p (car iter))
                  (not (consp iter))))
  :enable tree-iter-p)

(defrule tree-empty-p-of-car-when-tree-iter-p-cheap
  (implies (tree-iter-p iter)
           (equal (tree-empty-p (car iter))
                  (not (consp iter))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-empty-p-of-car-when-tree-iter-p)

(defrule tree-iter-p-of-cdr
  (implies (tree-iter-p iter)
           (tree-iter-p (cdr iter)))
  :enable tree-iter-p)

;; TODO: unused?
(defrule tree-iter-p-of-append
  (implies (tree-iter-p x)
           (equal (tree-iter-p (append x y))
                  (tree-iter-p y)))
  :induct t
  :enable tree-iter-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Check that all elements of a tree list are bsts and heaps

(define all-well-formed-p ((trees tree-listp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (endp trees)
      (and (bstp (first trees))
           (heapp (first trees))
           (all-well-formed-p (rest trees)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t all-well-formed-p)))

(defrule bstp-when-all-well-formed-p
  (implies (and (all-well-formed-p trees)
                (member-equal tree trees))
           (bstp tree))
  :induct t
  :enable (all-well-formed-p
           member-equal))

(defrule heapp-when-all-well-formed-p
  (implies (and (all-well-formed-p trees)
                (member-equal tree trees))
           (heapp tree))
  :induct t
  :enable (all-well-formed-p
           member-equal))

(defrule bstp-of-car-when-all-well-formed-p
  (implies (all-well-formed-p trees)
           (bstp (car trees)))
  :enable all-well-formed-p)

(defrule heapp-of-car-when-all-well-formed-p
  (implies (all-well-formed-p trees)
           (heapp (car trees)))
  :enable all-well-formed-p)

(defrule bstp-of-car-last-when-all-well-formed-p
  (implies (all-well-formed-p trees)
           (bstp (car (last trees))))
  :induct t
  :enable (last
           all-well-formed-p))

(defrule heapp-of-car-last-when-all-well-formed-p
  (implies (all-well-formed-p trees)
           (heapp (car (last trees))))
  :induct t
  :enable (last
           all-well-formed-p))

;; Used by tree-left-spine theorem
(defrule all-well-formed-p-of-append
  (equal (all-well-formed-p (append x y))
         (and (all-well-formed-p x)
              (all-well-formed-p y)))
  :induct t
  :enable all-well-formed-p)

(defrule all-well-formed-p-of-singleton
  (equal (all-well-formed-p (cons tree nil))
         (and (bstp tree)
              (heapp tree)))
  :enable all-well-formed-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An element of the iterator list is a subset of the left child of the next
;; tree in the list.
;; This is a little awkward because we have to look at elements pairwise.
;; Note that this is weaker than the true invariant we expect, which is that an
;; element of the iterator list is exactly one of the trees in the right spine
;; of the left child of the next tree in the list.
;; The weaker invariant is sufficient for our needs.
;; (It wouldn't be sufficient to show uniqueness of iterators, but we don't
;; care about that).

(define pairwise-tree-subset-p-of-left-loop ((iter tree-iter-p))
  :guard (and (consp iter)
              (all-well-formed-p iter))
  (or (endp (rest iter))
      (and (tree-subset-p (first iter) (tree->left (second iter)))
           (pairwise-tree-subset-p-of-left-loop (rest iter))))
  :hints (("Goal" :in-theory (enable acl2-count)))
  :guard-hints (("Goal" :in-theory (enable all-well-formed-p))))

(define pairwise-tree-subset-p-of-left ((iter tree-iter-p))
  :guard (all-well-formed-p iter)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (endp iter)
      (mbe :logic (or (endp (rest iter))
                      (and (tree-subset-p (first iter)
                                          (tree->left (second iter)))
                           (pairwise-tree-subset-p-of-left (rest iter))))
           :exec (pairwise-tree-subset-p-of-left-loop iter)))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t pairwise-tree-subset-p-of-left)))

(defrulel loop-becomes-pairwise-tree-subset-p-of-left
  (implies (consp iter)
           (equal (pairwise-tree-subset-p-of-left-loop iter)
                  (pairwise-tree-subset-p-of-left iter)))
  :induct t
  :enable (pairwise-tree-subset-p-of-left-loop
           pairwise-tree-subset-p-of-left))

(verify-guards pairwise-tree-subset-p-of-left
  :hints (("Goal" :in-theory (enable pairwise-tree-subset-p-of-left))))

(defrule pairwise-tree-subset-p-of-left-of-append
  (equal (pairwise-tree-subset-p-of-left (append x y))
         (and (pairwise-tree-subset-p-of-left x)
              (pairwise-tree-subset-p-of-left y)
              (or (not (consp x))
                  (not (consp y))
                  (tree-subset-p (car (last x))
                                 (tree->left (first y))))))
  :induct t
  :enable (append
           pairwise-tree-subset-p-of-left
           last))

(defrule tree-subset-p-of-car-when-member-equal
  (implies (and (pairwise-tree-subset-p-of-left iter)
                (member-equal tree iter))
           (tree-subset-p (car iter) tree))
  :induct t
  :enable pairwise-tree-subset-p-of-left)

(defrule tree-subset-p-of-car-and-car-last
  (implies (pairwise-tree-subset-p-of-left iter)
           (tree-subset-p (car iter) (car (last iter))))
  :induct t
  :enable pairwise-tree-subset-p-of-left)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; As described for tree-iter-p, an iterator is interpreted as representing
;; the sequence of the head of its car, then the right elements in order, then
;; the rest of the iterator.

(define tree-iter-to-tree ((iter tree-iter-p))
  :returns (tree treep)
  :parents (implementation)
  :short "Construct a tree from a tree iterator."
  :long
  (xdoc::topstring
   (xdoc::p
     "This function is not currently optimal when we know that @('iter') is
      @('all-well-formed-p') and @('pairwise-tree-subset-p-of-left'). In such a
      case, it would be optimal to simply set the first tree to be the left
      subtree of the following tree, and recurse. This would be possible
      because we know all elements of the first tree to be smaller than those
      of the following tree (considering only the iterator-relevant
      elements)."))
  (if (endp iter)
      nil
    (mv-let (in tree)
            (tree-insert (tagged-element->elem (tree->head (first iter)))
                         (tagged-element->hash (tree->head (first iter)))
                         (tree-union (tree->right (first iter))
                                     (tree-iter-to-tree (rest iter))))
      (declare (ignore in))
      tree))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter-to-tree)))

(defrule tree-iter-to-tree-type-prescription
  (or (consp (tree-iter-to-tree tree))
      (equal (tree-iter-to-tree tree) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-iter-to-tree)

(defrule tree-empty-p-of-tree-iter-to-tree
  (equal (tree-empty-p (tree-iter-to-tree iter))
         (not (consp iter)))
  :expand (tree-iter-to-tree iter))

(defrule tree-iter-to-tree-when-not-consp-cheap
  (implies (not (consp iter))
           (equal (tree-iter-to-tree iter)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-iter-to-tree)

(defrule bstp-of-tree-iter-to-tree
  (implies (all-well-formed-p iter)
           (bstp (tree-iter-to-tree iter)))
  :induct t
  :enable (tree-iter-to-tree
           all-well-formed-p))

(defrule heapp-of-tree-iter-to-tree
  (implies (all-well-formed-p iter)
           (heapp (tree-iter-to-tree iter)))
  :induct t
  :enable (tree-iter-to-tree
           all-well-formed-p))

;;;;;;;;;;;;;;;;;;;;

(defruled tree-in-of-tree-iter-to-tree
  (implies (all-well-formed-p trees)
           (equal (tree-in elem (tree-iter-to-tree trees))
                  (and (consp trees)
                       (or (equal elem (tagged-element->elem
                                         (tree->head (car trees))))
                           (tree-in elem (tree->right (car trees)))
                           (tree-in elem (tree-iter-to-tree (cdr trees)))))))
  :enable (tree-iter-to-tree
           all-well-formed-p))

(defruled tree-in-of-tree-iter-to-tree-of-cons
  (implies (and (bstp tree)
                (all-well-formed-p trees))
           (equal (tree-in elem (tree-iter-to-tree (cons tree trees)))
                  (or (equal elem (tagged-element->elem (tree->head tree)))
                      (tree-in elem (tree->right tree))
                      (tree-in elem (tree-iter-to-tree trees)))))
  :enable (tree-iter-to-tree
           all-well-formed-p))

;;;;;;;;;;;;;;;;;;;;

(defruled tree-in-of-tree-iter-to-tree-of-append
  (implies (and (all-well-formed-p x)
                (all-well-formed-p y))
           (equal (tree-in elem (tree-iter-to-tree (append x y)))
                  (or (tree-in elem (tree-iter-to-tree x))
                      (tree-in elem (tree-iter-to-tree y)))))
  :induct t
  :enable (tree-iter-to-tree
           all-well-formed-p))

(defrule tree-iter-to-tree-of-append
  (implies (and (all-well-formed-p x)
                (all-well-formed-p y))
           (equal (tree-iter-to-tree (append x y))
                  (tree-union (tree-iter-to-tree x)
                              (tree-iter-to-tree y))))
  :enable (tree-double-containment-no-backchain-limit
           tree-in-of-tree-iter-to-tree-of-append
           tree-subset-p-becomes-tree-subset-p-sk
           tree-subset-p-sk))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-left-spine-acc
  ((tree treep)
   (acc tree-listp))
  :returns (spine tree-listp)
  (if (tree-empty-p tree)
      (tree-list-fix acc)
    (tree-left-spine-acc (tree->left tree)
                         (cons (tree-fix tree) (tree-list-fix acc)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-left-spine-acc)))

(defrule tree-left-spine-acc-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-left-spine-acc tree0 acc)
                  (tree-left-spine-acc tree1 acc)))
  :rule-classes :congruence
  :expand ((tree-left-spine-acc tree0 acc)
           (tree-left-spine-acc tree1 acc)))

(defrulel tree-left-spine-acc-of-arg1-and-tree-list-fix
  (equal (tree-left-spine-acc tree (tree-list-fix acc))
         (tree-left-spine-acc tree acc))
  :expand ((tree-left-spine-acc tree (tree-list-fix acc))
           (tree-left-spine-acc tree acc)))

(defruledl tree-left-spine-acc-of-append
  (implies (and (tree-listp x)
                (tree-listp y))
           (equal (tree-left-spine-acc tree (append x y))
                  (append (tree-left-spine-acc tree x)
                          y)))
  :induct t
  :enable tree-left-spine-acc)

(defruled tree-left-spine-acc-arg2-becomes-nil
  (equal (tree-left-spine-acc tree acc)
         (append (tree-left-spine-acc tree nil)
                 (tree-list-fix acc)))
  :use (:instance tree-left-spine-acc-of-append
                  (x nil)
                  (y (tree-list-fix acc))))

(defrule tree-left-spine-acc-arg2-becomes-nil-syntaxp
  (implies (syntaxp (not (equal acc ''nil)))
           (equal (tree-left-spine-acc tree acc)
                  (append (tree-left-spine-acc tree nil)
                          (tree-list-fix acc))))
  :by tree-left-spine-acc-arg2-becomes-nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: this serves as the iterator constructor, in addition to being used in
;; the "next" function.
(define tree-left-spine ((tree treep))
  :returns (spine tree-listp)
  (mbe :logic (if (tree-empty-p tree)
                  nil
                (append (tree-left-spine (tree->left tree))
                        (list (tree-fix tree))))
       :exec (tree-left-spine-acc tree nil))
  :inline t
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-left-spine)))

(defrule tree-left-spine-type-prescription
  (true-listp (tree-left-spine tree))
  :rule-classes :type-prescription
  :induct t
  :enable tree-left-spine)

(defrule tree-left-spine-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-left-spine tree0)
                  (tree-left-spine tree1)))
  :rule-classes :congruence
  :expand ((tree-left-spine tree0)
           (tree-left-spine tree1)))

(defrule tree-left-spine-acc-becomes-tree-left-spine
  (equal (tree-left-spine-acc tree acc)
         (append (tree-left-spine tree)
                 (tree-list-fix acc)))
  :induct t
  :enable (tree-left-spine-acc
           tree-left-spine))

(verify-guards tree-left-spine$inline
  :hints (("Goal" :in-theory (enable tree-left-spine))))

(defrule tree-iter-p-tree-left-spine
  (tree-iter-p (tree-left-spine tree))
  :induct t
  :enable (tree-left-spine
           tree-iter-p))

(defrule car-last-of-tree-left-spine
  (equal (car (last (tree-left-spine tree)))
         (tree-fix tree))
  :induct t
  :enable (tree-left-spine
           last))

(defrule all-well-formed-of-tree-left-spine
  (implies (and (bstp tree)
                (heapp tree))
           (all-well-formed-p (tree-left-spine tree)))
  :induct t
  :enable (tree-left-spine
           all-well-formed-p))

(defrule pairwise-tree-subset-p-of-left-of-tree-left-spine
  (pairwise-tree-subset-p-of-left (tree-left-spine tree))
  :induct t
  :enable (tree-left-spine
           pairwise-tree-subset-p-of-left))

;;;;;;;;;;;;;;;;;;;;

(defruledl tree-in-tree-iter-to-tree-of-tree-left-spine
  (implies (and (bstp tree)
                (heapp tree))
           (equal (tree-in x (tree-iter-to-tree (tree-left-spine tree)))
                  (tree-in x tree)))
  :induct t
  :enable (tree-iter-to-tree
           tree-left-spine))

(defrule tree-iter-to-tree-of-tree-left-spine
  (implies (and (treep tree)
                (bstp tree)
                (heapp tree))
           (equal (tree-iter-to-tree (tree-left-spine tree))
                  tree))
  :enable (tree-double-containment-no-backchain-limit
           tree-in-tree-iter-to-tree-of-tree-left-spine
           tree-subset-p-becomes-tree-subset-p-sk
           tree-subset-p-sk))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-value ((iter tree-iter-p))
  :guard (not (endp iter))
  (tagged-element->elem (tree->head (first iter)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-iter-p))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-tree-iter-value
  (equal (tree-in (tree-iter-value iter) (tree-iter-to-tree iter))
         (consp iter))
  :induct t
  :enable (tree-iter-to-tree
           tree-iter-value))

(defrulel <<-all-r-of-tree->head-and-tree-iter-to-tree
  (implies (and (tree-iter-p iter)
                (all-well-formed-p iter)
                (pairwise-tree-subset-p-of-left iter))
           (<<-all-r (tagged-element->elem (tree->head (car iter)))
                     (tree-iter-to-tree (cdr iter))))
  :induct t
  :enable (tree-iter-p
            all-well-formed-p
            pairwise-tree-subset-p-of-left
            tree-iter-to-tree
            tree-in-extra-rules
            <<-all-extra-rules))

(defruled tree-iter-value-becomes-tree-min
  (implies (and (tree-iter-p iter)
                (all-well-formed-p iter)
                (pairwise-tree-subset-p-of-left iter))
           (equal (tree-iter-value iter)
                  (tree-min (tree-iter-to-tree iter))))
  :induct t
  :enable (tree-iter-value
           tree-iter-to-tree
           tree-min-of-tree-insert-when-<<-all-r))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-next ((iter tree-iter-p))
  :guard (not (endp iter))
  :returns (next tree-iter-p)
  (let* ((iter (mbe :logic (if (tree-iter-p iter)
                               iter
                             nil)
                    :exec iter))
         (rest-iter (rest (the cons iter)))
         (right (tree->right (first (the cons iter)))))
    (if (tree-empty-p right)
        rest-iter
      (mbe :logic (append (tree-left-spine right)
                          rest-iter)
           :exec (tree-left-spine-acc right rest-iter)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter-next)))

(defrule tree-iter-next-type-prescription
  (true-listp (tree-iter-next tree))
  :rule-classes :type-prescription
  :enable tree-iter-next)

(defrule all-well-formed-p-of-tree-iter-next
  (implies (all-well-formed-p iter)
           (all-well-formed-p (tree-iter-next iter)))
  :enable (tree-iter-next
           all-well-formed-p))

(defrule pairwise-tree-subset-p-of-left-of-tree-iter-next
  (implies (pairwise-tree-subset-p-of-left iter)
           (pairwise-tree-subset-p-of-left (tree-iter-next iter)))
  :enable (tree-iter-next
           pairwise-tree-subset-p-of-left))

(defruledl tree-in-tree-iter-to-tree-of-tree-iter-next
  (implies (and (tree-iter-p iter)
                (all-well-formed-p iter)
                (pairwise-tree-subset-p-of-left iter))
           (equal (tree-in x (tree-iter-to-tree (tree-iter-next iter)))
                  (tree-in x (tree-delete (tree-iter-value iter)
                                          (tree-iter-to-tree iter)))))
  :enable (tree-iter-value
           tree-iter-next
           tree-iter-to-tree
           tree-iter-p
           all-well-formed-p
           tree-in-extra-rules))

(defrule tree-iter-to-tree-of-tree-iter-next
  (implies (and (tree-iter-p iter)
                (all-well-formed-p iter)
                (pairwise-tree-subset-p-of-left iter))
           (equal (tree-iter-to-tree (tree-iter-next iter))
                  (tree-delete (tree-iter-value iter)
                               (tree-iter-to-tree iter))))
  :enable (tree-double-containment-no-backchain-limit
           tree-in-tree-iter-to-tree-of-tree-iter-next
           tree-subset-p-becomes-tree-subset-p-sk
           tree-subset-p-sk))
