; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/osets/defs" :dir :system)

(include-book "../../internal/tree-defs")
(include-book "../../internal/bst-defs")
(include-book "../../internal/heap-defs")
(include-book "../../internal/in-defs")
(include-book "../../internal/in-order-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (include-book "../../internal/tree"))
(local (include-book "../../internal/bst"))
(local (include-book "../../internal/heap"))
(local (include-book "../../internal/in"))
(local (include-book "../../internal/in-order"))
(local (include-book "../../internal/subset"))
(local (include-book "zip-frame"))
(local (include-book "zipper"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

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

(defruledl tree-subset-p-of-tree-nodes-sharing-left
  (implies (tree-subset-p acc tree)
           (tree-subset-p (tree-node head sibling acc)
                          (tree-node head sibling tree)))
  :enable (tree-subset-p
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->left
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->right))

(defruledl tree-subset-p-of-tree-nodes-sharing-right
  (implies (tree-subset-p acc tree)
           (tree-subset-p (tree-node head acc sibling)
                          (tree-node head tree sibling)))
  :enable (tree-subset-p
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->left
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (xdoc::set-default-parents zipper))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-path-tree-before ((path zip-frame-listp)
                              (acc treep))
  :returns (tree treep)
  :short "The elements which precede the focus subtree, as a tree atop an
          accumulator."
  (if (acl2::endp path)
      (tree-fix acc)
    (zip-path-tree-before
      (rest path)
      (if (zip-frame->from-left (first path))
          acc
        (tree-node (zip-frame->elem (first path))
                   (zip-frame->sibling (first path))
                   acc))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-path-tree-after ((path zip-frame-listp)
                             (acc treep))
  :returns (tree treep)
  :short "The elements which follow the focus subtree, as a tree atop an
          accumulator."
  (if (acl2::endp path)
      (tree-fix acc)
    (zip-path-tree-after
      (rest path)
      (if (zip-frame->from-left (first path))
          (tree-node (zip-frame->elem (first path))
                     acc
                     (zip-frame->sibling (first path)))
        acc)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-path-tree-before-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv acc0 acc1)
           (equal (zip-path-tree-before path acc0)
                  (zip-path-tree-before path acc1)))
  :rule-classes :congruence
  :induct t
  :enable zip-path-tree-before)

(defrule zip-path-tree-after-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv acc0 acc1)
           (equal (zip-path-tree-after path acc0)
                  (zip-path-tree-after path acc1)))
  :rule-classes :congruence
  :induct t
  :enable zip-path-tree-after)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-tree-before ((zip zipp))
  :returns (tree treep)
  :short "The elements which precede the cursor, as a tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth of the focus, and
      so @($O(\\log(n))$) over a @(see tset). One node is built per
      contributing frame; every subtree hangs off the original tree
      unchanged."))
  (zip-path-tree-before (zip->path zip)
                        (tree->left (zip->focus zip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-tree-after ((zip zipp))
  :returns (tree treep)
  :short "The elements which follow the cursor, as a tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth of the focus, and
      so @($O(\\log(n))$) over a @(see tset). One node is built per
      contributing frame; every subtree hangs off the original tree
      unchanged."))
  (zip-path-tree-after (zip->path zip)
                       (tree->right (zip->focus zip))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-tree-before-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-tree-before zip0)
                  (zip-tree-before zip1)))
  :rule-classes :congruence
  :enable zip-tree-before)

(defrule zip-tree-after-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-tree-after zip0)
                  (zip-tree-after zip1)))
  :rule-classes :congruence
  :enable zip-tree-after)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-path-before ((path zip-frame-listp))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The values which precede the focus subtree, in order."
  (if (acl2::endp path)
      nil
    (append (zip-path-before (rest path))
            (if (zip-frame->from-left (first path))
                nil
              (append (tree-in-order (zip-frame->sibling (first path)))
                      (list (tree-element->val
                              (zip-frame->elem (first path))))))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-path-after ((path zip-frame-listp))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The values which follow the focus subtree, in order."
  (if (acl2::endp path)
      nil
    (append (if (zip-frame->from-left (first path))
                (cons (tree-element->val (zip-frame->elem (first path)))
                      (tree-in-order (zip-frame->sibling (first path))))
              nil)
            (zip-path-after (rest path))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-path-before-when-not-consp-cheap
  (implies (not (consp path))
           (equal (zip-path-before path)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable zip-path-before)

(defrule zip-path-after-when-not-consp-cheap
  (implies (not (consp path))
           (equal (zip-path-after path)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable zip-path-after)

(defrule zip-path-before-of-cons
  (equal (zip-path-before (cons frame path))
         (append (zip-path-before path)
                 (if (zip-frame->from-left frame)
                     nil
                   (append (tree-in-order (zip-frame->sibling frame))
                           (list (tree-element->val
                                   (zip-frame->elem frame)))))))
  :enable zip-path-before)

(defrule zip-path-after-of-cons
  (equal (zip-path-after (cons frame path))
         (append (if (zip-frame->from-left frame)
                     (cons (tree-element->val (zip-frame->elem frame))
                           (tree-in-order (zip-frame->sibling frame)))
                   nil)
                 (zip-path-after path)))
  :enable zip-path-after)

(defruled zip-path-after-when-zip-path-no-left-frames-p
  (implies (zip-path-no-left-frames-p path)
           (equal (zip-path-after path)
                  nil))
  :induct t
  :enable zip-path-no-left-frames-p)

(defrule zip-path-after-when-zip-path-no-left-frames-p-forward-chaining
  (implies (zip-path-no-left-frames-p path)
           (equal (zip-path-after path)
                  nil))
  :rule-classes :forward-chaining
  :by zip-path-after-when-zip-path-no-left-frames-p)

(defruled zip-path-before-when-zip-path-no-right-frames-p
  (implies (zip-path-no-right-frames-p path)
           (equal (zip-path-before path)
                  nil))
  :induct t
  :enable zip-path-no-right-frames-p)

(defrule zip-path-before-when-zip-path-no-right-frames-p-forward-chaining
  (implies (zip-path-no-right-frames-p path)
           (equal (zip-path-before path)
                  nil))
  :rule-classes :forward-chaining
  :by zip-path-before-when-zip-path-no-right-frames-p)

(defrule zip-path-no-left-frames-p-when-not-consp-of-zip-path-after
  (implies (not (consp (zip-path-after path)))
           (zip-path-no-left-frames-p path))
  :induct t
  :enable zip-path-no-left-frames-p)

(defrule zip-path-no-right-frames-p-when-not-consp-of-zip-path-before
  (implies (not (consp (zip-path-before path)))
           (zip-path-no-right-frames-p path))
  :induct t
  :enable zip-path-no-right-frames-p)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-order-of-zip-path-tree-before
  (equal (tree-in-order (zip-path-tree-before path acc))
         (append (zip-path-before path)
                 (tree-in-order acc)))
  :induct t
  :enable (zip-path-tree-before
           tree-in-order))

(defrule tree-in-order-of-zip-path-tree-after
  (equal (tree-in-order (zip-path-tree-after path acc))
         (append (tree-in-order acc)
                 (zip-path-after path)))
  :induct t
  :enable (zip-path-tree-after
           tree-in-order))

(defrule tree-empty-p-of-zip-path-tree-before
  (equal (tree-empty-p (zip-path-tree-before path acc))
         (and (not (consp (zip-path-before path)))
              (tree-empty-p acc)))
  :induct t
  :enable zip-path-tree-before)

(defrule tree-empty-p-of-zip-path-tree-after
  (equal (tree-empty-p (zip-path-tree-after path acc))
         (and (not (consp (zip-path-after path)))
              (tree-empty-p acc)))
  :induct t
  :enable zip-path-tree-after)

(defrule tree-in-of-zip-path-tree-before
  (equal (tree-in x (zip-path-tree-before path acc))
         (or (and (member-equal x (zip-path-before path)) t)
             (tree-in x acc)))
  :induct t
  :enable zip-path-tree-before)

(defrule tree-in-of-zip-path-tree-after
  (equal (tree-in x (zip-path-tree-after path acc))
         (or (and (member-equal x (zip-path-after path)) t)
             (tree-in x acc)))
  :induct t
  :enable zip-path-tree-after)

(defrule tree-in-order-of-zip-path-plug
  (equal (tree-in-order (zip-path-plug path tree))
         (append (zip-path-before path)
                 (tree-in-order tree)
                 (zip-path-after path)))
  :induct t
  :enable (zip-path-plug
           zip-frame-plug
           tree-in-order))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-value ((zip zipp))
  :guard (not (tree-empty-p (zip->focus zip)))
  :short "The value of the element the zipper is at."
  (tree-element->val (tree->head (zip->focus zip)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-value-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-value zip0)
                  (zip-value zip1)))
  :rule-classes :congruence
  :enable zip-value)

(defruled zip-value-when-tree-empty-p-of-focus
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-value zip)
                  nil))
  :enable (zip-value
           irr-tree-element))

(defrule zip-value-when-tree-empty-p-of-focus-cheap
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-value zip)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by zip-value-when-tree-empty-p-of-focus)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-before ((zip zipp))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The values which precede the cursor, in order."
  (append (zip-path-before (zip->path zip))
          (tree-in-order (tree->left (zip->focus zip)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-after ((zip zipp))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The values which follow the cursor, in order."
  (append (tree-in-order (tree->right (zip->focus zip)))
          (zip-path-after (zip->path zip))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-before-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-before zip0)
                  (zip-before zip1)))
  :rule-classes :congruence
  :enable zip-before)

(defrule zip-after-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-after zip0)
                  (zip-after zip1)))
  :rule-classes :congruence
  :enable zip-after)

(defrule tree-in-order-of-zip-tree-before
  (equal (tree-in-order (zip-tree-before zip))
         (zip-before zip))
  :enable (zip-tree-before
           zip-before))

(defrule tree-in-order-of-zip-tree-after
  (equal (tree-in-order (zip-tree-after zip))
         (zip-after zip))
  :enable (zip-tree-after
           zip-after))

(defrule tree-empty-p-of-zip-tree-before
  (equal (tree-empty-p (zip-tree-before zip))
         (not (consp (zip-before zip))))
  :enable (not
           zip-tree-before
           zip-before))

(defrule tree-empty-p-of-zip-tree-after
  (equal (tree-empty-p (zip-tree-after zip))
         (not (consp (zip-after zip))))
  :enable (not
           zip-tree-after
           zip-after))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-order-of-zip-plug
  (equal (tree-in-order (zip-plug zip))
         (append (zip-path-before (zip->path zip))
                 (tree-in-order (zip->focus zip))
                 (zip-path-after (zip->path zip))))
  :enable zip-plug)

;; The same sequence, cut at the cursor instead of at the focus subtree.

(defruled tree-in-order-of-zip-plug-split-at-cursor
  (equal (tree-in-order (zip-plug zip))
         (append (zip-before zip)
                 (if (tree-empty-p (zip->focus zip))
                     (zip-after zip)
                   (cons (zip-value zip)
                         (zip-after zip)))))
  :enable (zip-before
           zip-after
           zip-value
           tree-in-order))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-oset-before ((zip zipp))
  :returns (oset set::setp)
  :short "The elements which precede the cursor, as an oset."
  (tree-oset (zip-tree-before zip)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-oset-after ((zip zipp))
  :returns (oset set::setp)
  :short "The elements which follow the cursor, as an oset."
  (tree-oset (zip-tree-after zip)))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-oset-before-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-oset-before zip0)
                  (zip-oset-before zip1)))
  :rule-classes :congruence
  :enable zip-oset-before)

(defrule zip-oset-after-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-oset-after zip0)
                  (zip-oset-after zip1)))
  :rule-classes :congruence
  :enable zip-oset-after)

(defrule tree-oset-of-zip-tree-before
  (equal (tree-oset (zip-tree-before zip))
         (zip-oset-before zip))
  :enable zip-oset-before)

(defrule tree-oset-of-zip-tree-after
  (equal (tree-oset (zip-tree-after zip))
         (zip-oset-after zip))
  :enable zip-oset-after)

(defrule in-of-zip-oset-before
  (iff (set::in x (zip-oset-before zip))
       (member-equal x (zip-before zip)))
  :enable (zip-oset-before
           zip-tree-before
           zip-before)
  :disable tree-oset-of-zip-tree-before)

(defrule in-of-zip-oset-after
  (iff (set::in x (zip-oset-after zip))
       (member-equal x (zip-after zip)))
  :enable (zip-oset-after
           zip-tree-after
           zip-after)
  :disable tree-oset-of-zip-tree-after)

(defrule tree-in-of-zip-tree-before
  (equal (tree-in x (zip-tree-before zip))
         (set::in x (zip-oset-before zip)))
  :enable zip-oset-before
  :disable tree-oset-of-zip-tree-before)

(defrule tree-in-of-zip-tree-after
  (equal (tree-in x (zip-tree-after zip))
         (set::in x (zip-oset-after zip)))
  :enable zip-oset-after
  :disable tree-oset-of-zip-tree-after)

(defrule emptyp-of-zip-oset-before
  (equal (set::emptyp (zip-oset-before zip))
         (not (consp (zip-before zip))))
  :enable zip-oset-before
  :disable tree-oset-of-zip-tree-before)

(defrule emptyp-of-zip-oset-after
  (equal (set::emptyp (zip-oset-after zip))
         (not (consp (zip-after zip))))
  :enable zip-oset-after
  :disable tree-oset-of-zip-tree-after)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel bstp-of-arg2-when-bstp-of-zip-path-plug-forward-chaining
  (implies (bstp (zip-path-plug path tree))
           (bstp tree))
  :rule-classes :forward-chaining)

(defrulel heapp-of-arg2-when-heapp-of-zip-path-plug-forward-chaining
  (implies (heapp (zip-path-plug path tree))
           (heapp tree))
  :rule-classes :forward-chaining)

(local
  (define zip-path-tree-before-induction ((path zip-frame-listp)
                                          (tree treep)
                                          (acc treep))
    :verify-guards nil
    :enabled t
    (if (acl2::endp path)
        (list tree acc)
      (zip-path-tree-before-induction
        (rest path)
        (zip-frame-plug (first path) tree)
        (if (zip-frame->from-left (first path))
            acc
          (tree-node (zip-frame->elem (first path))
                     (zip-frame->sibling (first path))
                     acc))))))

(local
  (define zip-path-tree-after-induction ((path zip-frame-listp)
                                         (tree treep)
                                         (acc treep))
    :verify-guards nil
    :enabled t
    (if (acl2::endp path)
        (list tree acc)
      (zip-path-tree-after-induction
        (rest path)
        (zip-frame-plug (first path) tree)
        (if (zip-frame->from-left (first path))
            (tree-node (zip-frame->elem (first path))
                       acc
                       (zip-frame->sibling (first path)))
          acc)))))

(defruledl bstp-of-zip-path-tree-before
  (implies (and (bstp (zip-path-plug path tree))
                (bstp acc)
                (tree-subset-p acc tree))
           (bstp (zip-path-tree-before path acc)))
  :induct (zip-path-tree-before-induction path tree acc)
  :enable (zip-path-tree-before
           zip-frame-plug
           <<-all-r-when-tree-subset-p
           tree-subset-p-of-tree-nodes-sharing-left
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->left)
  :disable zip-frame-elim)

(defruledl heapp-of-zip-path-tree-before
  (implies (and (heapp (zip-path-plug path tree))
                (heapp acc)
                (tree-subset-p acc tree))
           (heapp (zip-path-tree-before path acc)))
  :induct (zip-path-tree-before-induction path tree acc)
  :enable (zip-path-tree-before
           zip-frame-plug
           heap<-all-l-when-tree-subset-p
           tree-subset-p-of-tree-nodes-sharing-left
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->left)
  :disable (zip-frame-elim
            tree-node-elim))

(defruledl bstp-of-zip-path-tree-after
  (implies (and (bstp (zip-path-plug path tree))
                (bstp acc)
                (tree-subset-p acc tree))
           (bstp (zip-path-tree-after path acc)))
  :induct (zip-path-tree-after-induction path tree acc)
  :enable (zip-path-tree-after
           zip-frame-plug
           <<-all-l-when-tree-subset-p
           tree-subset-p-of-tree-nodes-sharing-right
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->right)
  :disable zip-frame-elim)

(defruledl heapp-of-zip-path-tree-after
  (implies (and (heapp (zip-path-plug path tree))
                (heapp acc)
                (tree-subset-p acc tree))
           (heapp (zip-path-tree-after path acc)))
  :induct (zip-path-tree-after-induction path tree acc)
  :enable (zip-path-tree-after
           zip-frame-plug
           heap<-all-l-when-tree-subset-p
           tree-subset-p-of-tree-nodes-sharing-right
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->right)
  :disable (zip-frame-elim
            tree-node-elim))

;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-zip-tree-before-when-bstp-of-zip-plug
  (implies (bstp (zip-plug zip))
           (bstp (zip-tree-before zip)))
  :enable (zip-tree-before
           zip-plug
           bstp-of-zip-path-tree-before))

(defrule heapp-of-zip-tree-before-when-heapp-of-zip-plug
  (implies (heapp (zip-plug zip))
           (heapp (zip-tree-before zip)))
  :enable (zip-tree-before
           zip-plug
           heapp-of-zip-path-tree-before))

(defrule bstp-of-zip-tree-after-when-bstp-of-zip-plug
  (implies (bstp (zip-plug zip))
           (bstp (zip-tree-after zip)))
  :enable (zip-tree-after
           zip-plug
           bstp-of-zip-path-tree-after))

(defrule heapp-of-zip-tree-after-when-heapp-of-zip-plug
  (implies (heapp (zip-plug zip))
           (heapp (zip-tree-after zip)))
  :enable (zip-tree-after
           zip-plug
           heapp-of-zip-path-tree-after))
