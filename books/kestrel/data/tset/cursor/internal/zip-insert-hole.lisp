; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "../../hash-defs")
(include-book "../../internal/tree-defs")
(include-book "../../internal/bst-defs")
(include-book "../../internal/heap-defs")
(include-book "../../internal/in-defs")
(include-book "../../internal/split-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")
(include-book "zip-move-defs")
(include-book "zip-side-defs")
(include-book "zip-seek-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/utilities/fixed-size-words/u32" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))

(local (include-book "../../hash"))
(local (include-book "../../internal/heap-order"))
(local (include-book "../../internal/tree"))
(local (include-book "../../internal/bst"))
(local (include-book "../../internal/heap"))
(local (include-book "../../internal/in"))
(local (include-book "../../internal/in-order"))
(local (include-book "../../internal/split"))
(local (include-book "../../internal/subset"))
(local (include-book "zip-frame"))
(local (include-book "zipper"))
(local (include-book "zip-move"))
(local (include-book "zip-side"))
(local (include-book "zip-seek"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (xdoc::set-default-parents zipper))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-ascend-while-lower
  (x
   (hash (unsigned-byte-p 32 hash))
   (zip zipp))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  :returns (zip$ zipp)
  :short "Move the focus up for as long as its parent is below a value in the
          heap order."
  :long
  (xdoc::topstring
   (xdoc::p
     "This finds the subtree which a new node for the value would sit on top
      of.")
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth of the focus. Over
      a @(see tset), the expected number of moves is constant."))
  (let ((path (zip->path zip)))
    (if (acl2::endp path)
        (zip-fix zip)
      (let ((elem (zip-frame->elem (first path))))
        (if (heap<-with-hashes (tree-element->val elem)
                               x
                               (tree-element->hash elem)
                               hash)
            (zip-ascend-while-lower x hash (zip-ascend-one zip))
          (zip-fix zip)))))
  :measure (len (zip->path zip))
  :guard-hints (("Goal" :in-theory (enable data::u32-equal))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-ascend-while-lower-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-ascend-while-lower x hash zip0)
                  (zip-ascend-while-lower x hash zip1)))
  :rule-classes :congruence
  :expand ((zip-ascend-while-lower x hash zip0)
           (zip-ascend-while-lower x hash zip1)))

(defrule zip-plug-of-zip-ascend-while-lower
  (equal (zip-plug (zip-ascend-while-lower x hash zip))
         (zip-plug zip))
  :induct t
  :enable zip-ascend-while-lower)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-insert-hole-loop
  (x
   (hash (unsigned-byte-p 32 hash))
   (focus treep)
   (path zip-frame-listp))
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  :short "Move up as @(tsee zip-ascend-while-lower) does, from a focus and a
          path, and put a new node for the value on top of the subtree
          reached."
  :long
  (xdoc::topstring-p
    "This is the form of @(tsee zip-insert-hole) to execute. It builds a
     single zipper, at the end.")
  (mbe :logic (let ((zip (zip-ascend-while-lower x hash (zip focus path))))
                (mv-let (in left right)
                        (tree-split x (zip->focus zip))
                  (declare (ignore in))
                  (zip (tree-node (tree-element (hash x) x) left right)
                       (zip->path zip))))
       :exec (if (and (consp path)
                      (let ((elem (zip-frame->elem (first path))))
                        (heap<-with-hashes (tree-element->val elem)
                                           x
                                           (tree-element->hash elem)
                                           hash)))
                 (zip-insert-hole-loop x
                                       hash
                                       (zip-frame-plug (first path) focus)
                                       (rest path))
               (mv-let (in left right)
                       (tree-split x focus)
                 (declare (ignore in))
                 (zip (tree-node (tree-element hash x) left right)
                      path))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable zip-insert-hole-loop
                                           zip-ascend-one
                                           data::u32-equal)
                        :expand ((zip-ascend-while-lower
                                   x (hash x) (zip focus path))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-insert-hole
  (x
   (zip zipp))
  :guard (tree-empty-p (zip->focus zip))
  :returns (zip$ zipp)
  :short "Add an element at the hole the zipper is at."
  :long
  (xdoc::topstring
   (xdoc::p
     "The value is assumed to belong at the hole: above every element before
      it and below every element after it. The new node goes above the nodes
      below it in the heap order, whose subtree is split around the value to
      make its children. The zipper is left at the new node.")
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth of the hole. Over
      a @(see tset), the expected time is constant, aside from hashing the
      value."))
  (mbe :logic (let* ((hash (hash x))
                     (zip (zip-ascend-while-lower x hash zip)))
                (mv-let (in left right)
                        (tree-split x (zip->focus zip))
                  (declare (ignore in))
                  (zip (tree-node (tree-element hash x) left right)
                       (zip->path zip))))
       :exec (zip-insert-hole-loop x
                                   (hash x)
                                   (zip->focus zip)
                                   (zip->path zip))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-insert-hole-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-insert-hole x zip0)
                  (zip-insert-hole x zip1)))
  :rule-classes :congruence
  :enable zip-insert-hole)

(defrule tree-empty-p-of-focus-of-zip-insert-hole
  (not (tree-empty-p (zip->focus (zip-insert-hole x zip))))
  :enable zip-insert-hole)

(defrule zip-value-of-zip-insert-hole
  (equal (zip-value (zip-insert-hole x zip))
         x)
  :enable (zip-insert-hole
           zip-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The ascent keeps the value bracketed by the path.

(defrulel zip-path-brackets-p-of-path-of-zip-ascend-while-lower
  (implies (zip-path-brackets-p y (zip->path zip))
           (zip-path-brackets-p y (zip->path
                                    (zip-ascend-while-lower x hash zip))))
  :induct (zip-ascend-while-lower x hash zip)
  :enable (zip-ascend-while-lower
           zip-path-brackets-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The ascent stops under a frame which is above the value in the heap order,
;; and everything it has passed is below the value.

(defrulel heapp-of-focus-when-heapp-of-zip-plug
  (implies (heapp (zip-plug zip))
           (heapp (zip->focus zip)))
  :enable zip-plug)

(defrulel heap<-all-l-of-focus-of-zip-ascend-while-lower
  (implies (and (heapp (zip-plug zip))
                (heap<-all-l (zip->focus zip) x))
           (heap<-all-l (zip->focus (zip-ascend-while-lower x hash zip))
                        x))
  :induct (zip-ascend-while-lower x hash zip)
  :enable (zip-ascend-while-lower
           zip-frame-plug
           heap<-all-l-weaken)
  :hints ('(:use (:instance heapp-of-focus-when-heapp-of-zip-plug
                            (zip (zip-ascend-one zip))))))

(defrulel not-heap<-of-first-frame-of-zip-ascend-while-lower
  (implies (consp (zip->path (zip-ascend-while-lower x hash zip)))
           (not (heap< (tree-element->val
                         (zip-frame->elem
                           (car (zip->path
                                  (zip-ascend-while-lower x hash zip)))))
                       x)))
  :induct (zip-ascend-while-lower x hash zip)
  :enable zip-ascend-while-lower)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A bound on the elements of a tree, and on one more value, bounds every tree
;; whose elements are among them. The tree with that one more value is
;; written as a node over the tree, with its element in normal form.

(defruledl <<-all-l-when-tree-subset-p-of-tree-node
  (implies (and (tree-subset-p new (tree-node (tree-element nil x) tree nil))
                (<< x y)
                (<<-all-l tree y))
           (<<-all-l new y))
  :use (:instance <<-all-l-when-tree-subset-p
                  (tree (tree-node (tree-element nil x) tree nil))
                  (acc new)
                  (x y)))

(defruledl <<-all-r-when-tree-subset-p-of-tree-node
  (implies (and (tree-subset-p new (tree-node (tree-element nil x) tree nil))
                (<< y x)
                (<<-all-r y tree))
           (<<-all-r y new))
  :use (:instance <<-all-r-when-tree-subset-p
                  (tree (tree-node (tree-element nil x) tree nil))
                  (acc new)
                  (x y)))

(defruledl heap<-all-l-when-tree-subset-p-of-tree-node
  (implies (and (tree-subset-p new (tree-node (tree-element nil x) tree nil))
                (heap< x y)
                (heap<-all-l tree y))
           (heap<-all-l new y))
  :use (:instance heap<-all-l-when-tree-subset-p
                  (tree (tree-node (tree-element nil x) tree nil))
                  (acc new)
                  (x y)))

(defruledl tree-in-when-tree-in-and-tree-subset-p-of-tree-node
  (implies (and (tree-subset-p new (tree-node (tree-element nil x) tree nil))
                (tree-in y new)
                (not (equal y x)))
           (tree-in y tree))
  :use (:instance tree-in-when-tree-in-and-tree-subset-p
                  (a y)
                  (x new)
                  (y (tree-node (tree-element nil x) tree nil)))
  :disable (tree-in-when-tree-in-and-tree-subset-p
            tree-in-when-tree-subset-p-and-tree-in))

;; That relation is kept when both trees are plugged into a frame.

(defruledl tree-subset-p-of-tree-nodes-when-tree-subset-p-of-tree-node
  (implies (tree-subset-p new (tree-node (tree-element nil x) tree nil))
           (and (tree-subset-p (tree-node head new sibling)
                               (tree-node (tree-element nil x)
                                          (tree-node head tree sibling)
                                          nil))
                (tree-subset-p (tree-node head sibling new)
                               (tree-node (tree-element nil x)
                                          (tree-node head sibling tree)
                                          nil))))
  :enable (tree-subset-p-pick-a-point-polar
           tree-in-when-tree-in-and-tree-subset-p-of-tree-node))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Replacing the focus by a tree with one more value keeps the order
;; invariant, when the path brackets the value.

(defrulel bstp-of-arg2-when-bstp-of-zip-path-plug-forward-chaining
  (implies (bstp (zip-path-plug path tree))
           (bstp tree))
  :rule-classes :forward-chaining)

(defrulel heapp-of-arg2-when-heapp-of-zip-path-plug-forward-chaining
  (implies (heapp (zip-path-plug path tree))
           (heapp tree))
  :rule-classes :forward-chaining)

(defrulel bstp-of-parts-when-bstp-of-tree-node-forward-chaining
  (implies (bstp (tree-node head left right))
           (and (bstp left)
                (bstp right)
                (<<-all-l left (tree-element->val head))
                (<<-all-r (tree-element->val head) right)))
  :rule-classes :forward-chaining)

(defrulel heapp-of-parts-when-heapp-of-tree-node-forward-chaining
  (implies (heapp (tree-node head left right))
           (and (heapp left)
                (heapp right)
                (heap<-all-l left (tree-element->val head))
                (heap<-all-l right (tree-element->val head))))
  :rule-classes :forward-chaining)

(local
  (define zip-path-plug-induction ((path zip-frame-listp)
                                   (tree treep)
                                   (new treep))
    :verify-guards nil
    :enabled t
    (if (acl2::endp path)
        (list tree new)
      (zip-path-plug-induction
        (rest path)
        (zip-frame-plug (first path) tree)
        (zip-frame-plug (first path) new)))))

(defruledl bstp-of-zip-path-plug-when-tree-subset-p-of-tree-node
  (implies (and (bstp (zip-path-plug path tree))
                (bstp new)
                (zip-path-brackets-p x path)
                (tree-subset-p new (tree-node (tree-element nil x) tree nil)))
           (bstp (zip-path-plug path new)))
  :induct (zip-path-plug-induction path tree new)
  :expand ((zip-path-plug path tree)
           (zip-path-plug path new))
  :enable (zip-frame-plug
           zip-path-brackets-p
           <<-all-l-when-tree-subset-p-of-tree-node
           <<-all-r-when-tree-subset-p-of-tree-node
           tree-subset-p-of-tree-nodes-when-tree-subset-p-of-tree-node))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Likewise for the heap invariant, when every frame of the path is above the
;; value in the heap order. In a heap, that holds of a whole path once it
;; holds of its first frame.

(local
  (define zip-path-heap-above-p
    (x
     (path zip-frame-listp))
    :returns (yes/no booleanp :rule-classes :type-prescription)
    :verify-guards nil
    (or (acl2::endp path)
        (and (heap< x (tree-element->val (zip-frame->elem (first path))))
             (zip-path-heap-above-p x (rest path))))))

(local
  (define zip-path-plug-induction1 ((path zip-frame-listp)
                                    (tree treep))
    :verify-guards nil
    :enabled t
    (if (acl2::endp path)
        tree
      (zip-path-plug-induction1 (rest path)
                                (zip-frame-plug (first path) tree)))))

(defruledl zip-path-heap-above-p-when-heap<-of-head
  (implies (and (heapp (zip-path-plug path tree))
                (not (tree-empty-p tree))
                (heap< x (tree-element->val (tree->head tree))))
           (zip-path-heap-above-p x path))
  :induct (zip-path-plug-induction1 path tree)
  :expand ((zip-path-plug path tree))
  :enable (zip-frame-plug
           zip-path-heap-above-p
           heap<-rules))

(defruledl zip-path-heap-above-p-when-heap<-of-first-frame
  (implies (and (heapp (zip-path-plug path tree))
                (consp path)
                (heap< x (tree-element->val (zip-frame->elem (car path)))))
           (zip-path-heap-above-p x path))
  :use (:instance zip-path-heap-above-p-when-heap<-of-head
                  (path (cdr path))
                  (tree (zip-frame-plug (car path) tree)))
  :expand ((zip-path-plug path tree))
  :enable (zip-frame-plug
           zip-path-heap-above-p))

(defruledl heapp-of-zip-path-plug-when-tree-subset-p-of-tree-node
  (implies (and (heapp (zip-path-plug path tree))
                (heapp new)
                (zip-path-heap-above-p x path)
                (tree-subset-p new (tree-node (tree-element nil x) tree nil)))
           (heapp (zip-path-plug path new)))
  :induct (zip-path-plug-induction path tree new)
  :expand ((zip-path-plug path tree)
           (zip-path-plug path new))
  :enable (zip-frame-plug
           zip-path-heap-above-p
           heap<-all-l-when-tree-subset-p-of-tree-node
           tree-subset-p-of-tree-nodes-when-tree-subset-p-of-tree-node))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The elements of a plugged tree, read off the elements around the focus.

(defruledl tree-in-of-zip-path-plug
  (equal (tree-in y (zip-path-plug path tree))
         (if (member-equal y (zip-path-before path))
             t
           (if (tree-in y tree)
               t
             (and (member-equal y (zip-path-after path))
                  t))))
  :use ((:instance tree-in-becomes-member-equal-of-tree-in-order
                   (x y)
                   (tree (zip-path-plug path tree)))
        (:instance tree-in-becomes-member-equal-of-tree-in-order
                   (x y)))
  :disable member-equal-of-tree-in-order-under-iff)

;; The new node, plugged in place of the tree it was split from, adds its
;; value and changes nothing else.

(defruledl tree-in-of-zip-path-plug-of-new-node
  (implies (bstp (zip-path-plug path tree))
           (equal (tree-in y
                           (zip-path-plug
                             path
                             (tree-node (tree-element hash x)
                                        (mv-nth 1 (tree-split x tree))
                                        (mv-nth 2 (tree-split x tree)))))
                  (or (equal y x)
                      (tree-in y (zip-path-plug path tree)))))
  :enable (tree-in-of-zip-path-plug
           data::<<-rules))

(defruledl tree-subset-p-of-new-node
  (implies (bstp tree)
           (tree-subset-p (tree-node (tree-element hash x)
                                     (mv-nth 1 (tree-split x tree))
                                     (mv-nth 2 (tree-split x tree)))
                          (tree-node (tree-element nil x) tree nil)))
  :enable tree-subset-p-pick-a-point-polar)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; So, at a hole whose path brackets the value, adding the element keeps the
;; invariants of the whole tree and adds just that element.

(defrulel zip-path-plug-of-path-and-focus
  (equal (zip-path-plug (zip->path zip) (zip->focus zip))
         (zip-plug zip))
  :enable zip-plug)

(defrulel bstp-of-focus-when-bstp-of-zip-plug
  (implies (bstp (zip-plug zip))
           (bstp (zip->focus zip)))
  :enable zip-plug
  :disable zip-path-plug-of-path-and-focus)

(defruledl bstp-of-zip-plug-of-zip-insert-hole-when-brackets
  (implies (and (bstp (zip-plug zip))
                (zip-path-brackets-p x (zip->path zip)))
           (bstp (zip-plug (zip-insert-hole x zip))))
  :use (:instance
         bstp-of-zip-path-plug-when-tree-subset-p-of-tree-node
         (path (zip->path (zip-ascend-while-lower x (hash x) zip)))
         (tree (zip->focus (zip-ascend-while-lower x (hash x) zip)))
         (new (tree-node
                (tree-element (hash x) x)
                (mv-nth 1 (tree-split
                            x
                            (zip->focus
                              (zip-ascend-while-lower x (hash x) zip))))
                (mv-nth 2 (tree-split
                            x
                            (zip->focus
                              (zip-ascend-while-lower x (hash x) zip)))))))
  :enable (zip-insert-hole
           tree-subset-p-of-new-node))

(defruledl heapp-of-zip-plug-of-zip-insert-hole-when-brackets
  (implies (and (heapp (zip-plug zip))
                (bstp (zip-plug zip))
                (tree-empty-p (zip->focus zip))
                (zip-path-brackets-p x (zip->path zip)))
           (heapp (zip-plug (zip-insert-hole x zip))))
  :use ((:instance
          heapp-of-zip-path-plug-when-tree-subset-p-of-tree-node
          (path (zip->path (zip-ascend-while-lower x (hash x) zip)))
          (tree (zip->focus (zip-ascend-while-lower x (hash x) zip)))
          (new (tree-node
                 (tree-element (hash x) x)
                 (mv-nth 1 (tree-split
                             x
                             (zip->focus
                               (zip-ascend-while-lower x (hash x) zip))))
                 (mv-nth 2 (tree-split
                             x
                             (zip->focus
                               (zip-ascend-while-lower x (hash x) zip)))))))
        (:instance
          zip-path-heap-above-p-when-heap<-of-first-frame
          (path (zip->path (zip-ascend-while-lower x (hash x) zip)))
          (tree (zip->focus (zip-ascend-while-lower x (hash x) zip))))
        (:instance
          zip-path-brackets-p-of-path-of-zip-ascend-while-lower
          (y x)
          (hash (hash x)))
        (:instance
          heap<-trichotomy
          (y (tree-element->val
               (zip-frame->elem
                 (car (zip->path
                        (zip-ascend-while-lower x (hash x) zip))))))))
  :expand ((zip-path-brackets-p
             x
             (zip->path (zip-ascend-while-lower x (hash x) zip))))
  :enable (zip-insert-hole
           zip-path-heap-above-p
           tree-subset-p-of-new-node
           heap<-all-l-of-tree-split.left-when-heap<-all-l
           heap<-all-l-of-tree-split.right-when-heap<-all-l
           heap<-all-l-when-tree-empty-p
           heap<-rules
           data::<<-rules)
  :disable zip-path-brackets-p-of-path-of-zip-ascend-while-lower)

(defruledl tree-in-of-zip-plug-of-zip-insert-hole-when-bstp
  (implies (bstp (zip-plug zip))
           (equal (tree-in y (zip-plug (zip-insert-hole x zip)))
                  (or (equal y x)
                      (tree-in y (zip-plug zip)))))
  :use (:instance
         tree-in-of-zip-path-plug-of-new-node
         (hash (hash x))
         (path (zip->path (zip-ascend-while-lower x (hash x) zip)))
         (tree (zip->focus (zip-ascend-while-lower x (hash x) zip))))
  :enable zip-insert-hole)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A search for a value which is not in the tree ends at such a hole.

(defrule bstp-of-zip-plug-of-zip-insert-hole-of-zip-seek
  (implies (bstp tree)
           (bstp (zip-plug (zip-insert-hole x (zip-seek x (zip-root tree))))))
  :enable bstp-of-zip-plug-of-zip-insert-hole-when-brackets)

(defrule heapp-of-zip-plug-of-zip-insert-hole-of-zip-seek
  (implies (and (bstp tree)
                (heapp tree)
                (not (tree-in x tree)))
           (heapp (zip-plug (zip-insert-hole x (zip-seek x (zip-root tree))))))
  :enable heapp-of-zip-plug-of-zip-insert-hole-when-brackets)

(defrule tree-in-of-zip-plug-of-zip-insert-hole-of-zip-seek
  (implies (bstp tree)
           (equal (tree-in y
                           (zip-plug
                             (zip-insert-hole x (zip-seek x (zip-root tree)))))
                  (or (equal y x)
                      (tree-in y tree))))
  :enable tree-in-of-zip-plug-of-zip-insert-hole-when-bstp)
