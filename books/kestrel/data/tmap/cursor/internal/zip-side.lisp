; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "kestrel/data/utilities/omap-defs" :dir :system)
(include-book "kestrel/data/tset/in-defs" :dir :system)

(include-book "../../internal/tree-defs")
(include-book "../../internal/bst-defs")
(include-book "../../internal/heap-defs")
(include-book "../../internal/keys-defs")
(include-book "../../internal/in-order-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))

(local (include-book "kestrel/data/utilities/omap" :dir :system))

(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (include-book "../../internal/tree"))
(local (include-book "../../internal/bst"))
(local (include-book "../../internal/heap"))
(local (include-book "../../internal/keys"))
(local (include-book "../../internal/in-order"))
(local (include-book "zip-frame"))
(local (include-book "zipper"))

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
      so @($O(\\log(n))$) over a @(see tmap). One node is built per
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
      so @($O(\\log(n))$) over a @(see tmap). One node is built per
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
  :short "The entries which precede the focus subtree, in order."
  (if (acl2::endp path)
      nil
    (append (zip-path-before (rest path))
            (if (zip-frame->from-left (first path))
                nil
              (append (tree-in-order (zip-frame->sibling (first path)))
                      (list (tree-element->key+val
                              (zip-frame->elem (first path))))))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-path-after ((path zip-frame-listp))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The entries which follow the focus subtree, in order."
  (if (acl2::endp path)
      nil
    (append (if (zip-frame->from-left (first path))
                (cons (tree-element->key+val (zip-frame->elem (first path)))
                      (tree-in-order (zip-frame->sibling (first path))))
              nil)
            (zip-path-after (rest path))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule alistp-of-zip-path-before
  (alistp (zip-path-before path))
  :induct t
  :enable zip-path-before)

(defrule alistp-of-zip-path-after
  (alistp (zip-path-after path))
  :induct t
  :enable zip-path-after)

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
                           (list (tree-element->key+val
                                   (zip-frame->elem frame)))))))
  :enable zip-path-before)

(defrule zip-path-after-of-cons
  (equal (zip-path-after (cons frame path))
         (append (if (zip-frame->from-left frame)
                     (cons (tree-element->key+val (zip-frame->elem frame))
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
           tree-in-order)
  :disable zip-frame-elim)

(defrule tree-in-order-of-zip-path-tree-after
  (equal (tree-in-order (zip-path-tree-after path acc))
         (append (tree-in-order acc)
                 (zip-path-after path)))
  :induct t
  :enable (zip-path-tree-after
           tree-in-order)
  :disable zip-frame-elim)

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

(defrule in-of-tree-key-set-of-zip-path-tree-before
  (equal (tset::in key (tree-key-set (zip-path-tree-before path acc)))
         (or (and (assoc-equal key (zip-path-before path)) t)
             (tset::in key (tree-key-set acc))))
  :induct t
  :enable (zip-path-tree-before
           zip-path-before
           assoc-equal-of-tree-in-order-under-iff)
  :disable zip-frame-elim)

(defrule in-of-tree-key-set-of-zip-path-tree-after
  (equal (tset::in key (tree-key-set (zip-path-tree-after path acc)))
         (or (and (assoc-equal key (zip-path-after path)) t)
             (tset::in key (tree-key-set acc))))
  :induct t
  :enable (zip-path-tree-after
           zip-path-after
           assoc-equal-of-tree-in-order-under-iff)
  :disable zip-frame-elim)

(defrule tree-in-order-of-zip-path-plug
  (equal (tree-in-order (zip-path-plug path tree))
         (append (zip-path-before path)
                 (tree-in-order tree)
                 (zip-path-after path)))
  :induct t
  :enable (zip-path-plug
           zip-frame-plug
           zip-path-before
           zip-path-after
           tree-in-order)
  :disable zip-frame-elim)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-key ((zip zipp))
  :guard (not (tree-empty-p (zip->focus zip)))
  :short "The key of the element the zipper is at."
  (tree-element->key (tree->head (zip->focus zip)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-key-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-key zip0)
                  (zip-key zip1)))
  :rule-classes :congruence
  :enable zip-key)

(defruled zip-key-when-tree-empty-p-of-focus
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-key zip)
                  nil))
  :enable (zip-key
           irr-tree-element))

(defrule zip-key-when-tree-empty-p-of-focus-cheap
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-key zip)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by zip-key-when-tree-empty-p-of-focus)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-val ((zip zipp))
  :guard (not (tree-empty-p (zip->focus zip)))
  :short "The value of the element the zipper is at."
  (tree-element->val (tree->head (zip->focus zip)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-val-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-val zip0)
                  (zip-val zip1)))
  :rule-classes :congruence
  :enable zip-val)

(defruled zip-val-when-tree-empty-p-of-focus
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-val zip)
                  nil))
  :enable (zip-val
           irr-tree-element))

(defrule zip-val-when-tree-empty-p-of-focus-cheap
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-val zip)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by zip-val-when-tree-empty-p-of-focus)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-key+val ((zip zipp))
  :guard (not (tree-empty-p (zip->focus zip)))
  :short "The key and value of the element the zipper is at, as a pair."
  (tree-element->key+val (tree->head (zip->focus zip)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-key+val-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-key+val zip0)
                  (zip-key+val zip1)))
  :rule-classes :congruence
  :enable zip-key+val)

(defruled zip-key+val-becomes-cons-of-zip-key-and-zip-val
  (equal (zip-key+val zip)
         (cons (zip-key zip) (zip-val zip)))
  :enable (zip-key+val
           zip-key
           zip-val
           tree-element->key+val
           tree-element->key
           tree-element->val))

(defrule zip-key+val-type-prescription
  (consp (zip-key+val zip))
  :rule-classes :type-prescription
  :enable zip-key+val-becomes-cons-of-zip-key-and-zip-val)

(defrule car-of-zip-key+val
  (equal (car (zip-key+val zip))
         (zip-key zip))
  :enable zip-key+val-becomes-cons-of-zip-key-and-zip-val)

(defrule cdr-of-zip-key+val
  (equal (cdr (zip-key+val zip))
         (zip-val zip))
  :enable zip-key+val-becomes-cons-of-zip-key-and-zip-val)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-before ((zip zipp))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The entries which precede the cursor, in order."
  (append (zip-path-before (zip->path zip))
          (tree-in-order (tree->left (zip->focus zip)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-after ((zip zipp))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The entries which follow the cursor, in order."
  (append (tree-in-order (tree->right (zip->focus zip)))
          (zip-path-after (zip->path zip))))

;;;;;;;;;;;;;;;;;;;;

(defrule alistp-of-zip-before
  (alistp (zip-before zip))
  :enable zip-before)

(defrule alistp-of-zip-after
  (alistp (zip-after zip))
  :enable zip-after)

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
                   (cons (zip-key+val zip)
                         (zip-after zip)))))
  :enable (zip-before
           zip-after
           zip-key+val
           tree-in-order))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-omap-before ((zip zipp))
  :returns (omap omap::mapp)
  :short "The entries which precede the cursor, as an omap."
  (tree-omap (zip-tree-before zip)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-omap-after ((zip zipp))
  :returns (omap omap::mapp)
  :short "The entries which follow the cursor, as an omap."
  (tree-omap (zip-tree-after zip)))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-omap-before-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-omap-before zip0)
                  (zip-omap-before zip1)))
  :rule-classes :congruence
  :enable zip-omap-before)

(defrule zip-omap-after-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-omap-after zip0)
                  (zip-omap-after zip1)))
  :rule-classes :congruence
  :enable zip-omap-after)

(defrule tree-omap-of-zip-tree-before
  (equal (tree-omap (zip-tree-before zip))
         (zip-omap-before zip))
  :enable zip-omap-before)

(defrule tree-omap-of-zip-tree-after
  (equal (tree-omap (zip-tree-after zip))
         (zip-omap-after zip))
  :enable zip-omap-after)

(theory-invariant
  (incompatible! (:definition zip-omap-before)
                 (:rewrite tree-omap-of-zip-tree-before)))

(theory-invariant
  (incompatible! (:definition zip-omap-after)
                 (:rewrite tree-omap-of-zip-tree-after)))

(defrule assoc-of-zip-omap-before-under-iff
  (iff (omap::assoc key (zip-omap-before zip))
       (assoc-equal key (zip-before zip)))
  :enable (zip-omap-before
           zip-tree-before
           zip-before
           assoc-equal-of-tree-in-order-under-iff)
  :disable tree-omap-of-zip-tree-before)

(defrule assoc-of-zip-omap-after-under-iff
  (iff (omap::assoc key (zip-omap-after zip))
       (assoc-equal key (zip-after zip)))
  :enable (zip-omap-after
           zip-tree-after
           zip-after
           assoc-equal-of-tree-in-order-under-iff)
  :disable tree-omap-of-zip-tree-after)

(defrule in-of-tree-key-set-of-zip-tree-before
  (equal (tset::in key (tree-key-set (zip-tree-before zip)))
         (and (omap::assoc key (zip-omap-before zip)) t))
  :enable zip-omap-before
  :disable tree-omap-of-zip-tree-before)

(defrule in-of-tree-key-set-of-zip-tree-after
  (equal (tset::in key (tree-key-set (zip-tree-after zip)))
         (and (omap::assoc key (zip-omap-after zip)) t))
  :enable zip-omap-after
  :disable tree-omap-of-zip-tree-after)

(defrule omap-emptyp-of-zip-omap-before
  (equal (omap::emptyp (zip-omap-before zip))
         (not (consp (zip-before zip))))
  :enable zip-omap-before
  :disable tree-omap-of-zip-tree-before)

(defrule omap-emptyp-of-zip-omap-after
  (equal (omap::emptyp (zip-omap-after zip))
         (not (consp (zip-after zip))))
  :enable zip-omap-after
  :disable tree-omap-of-zip-tree-after)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
                (tset::subset (tree-key-set acc) (tree-key-set tree)))
           (bstp (zip-path-tree-before path acc)))
  :induct (zip-path-tree-before-induction path tree acc)
  :enable (zip-path-tree-before
           zip-frame-plug
           <<-all-r-when-subset-of-tree-key-sets)
  :disable zip-frame-elim)

(defruledl heapp-of-zip-path-tree-before
  (implies (and (heapp (zip-path-plug path tree))
                (heapp acc)
                (tset::subset (tree-key-set acc) (tree-key-set tree)))
           (heapp (zip-path-tree-before path acc)))
  :induct (zip-path-tree-before-induction path tree acc)
  :enable (zip-path-tree-before
           zip-frame-plug
           heap<-all-l-when-subset-of-tree-key-sets)
  :disable (zip-frame-elim
            tree-node-elim))

(defruledl bstp-of-zip-path-tree-after
  (implies (and (bstp (zip-path-plug path tree))
                (bstp acc)
                (tset::subset (tree-key-set acc) (tree-key-set tree)))
           (bstp (zip-path-tree-after path acc)))
  :induct (zip-path-tree-after-induction path tree acc)
  :enable (zip-path-tree-after
           zip-frame-plug
           <<-all-l-when-subset-of-tree-key-sets)
  :disable zip-frame-elim)

(defruledl heapp-of-zip-path-tree-after
  (implies (and (heapp (zip-path-plug path tree))
                (heapp acc)
                (tset::subset (tree-key-set acc) (tree-key-set tree)))
           (heapp (zip-path-tree-after path acc)))
  :induct (zip-path-tree-after-induction path tree acc)
  :enable (zip-path-tree-after
           zip-frame-plug
           heap<-all-l-when-subset-of-tree-key-sets)
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

;;;;;;;;;;;;;;;;;;;;

;; Over a search tree, the omap of a side is its in-order list of entries.

(defruled zip-omap-before-becomes-zip-before
  (implies (bstp (zip-plug zip))
           (equal (zip-omap-before zip)
                  (zip-before zip)))
  :enable (zip-omap-before
           tree-omap-becomes-tree-in-order)
  :disable tree-omap-of-zip-tree-before)

(defruled zip-omap-after-becomes-zip-after
  (implies (bstp (zip-plug zip))
           (equal (zip-omap-after zip)
                  (zip-after zip)))
  :enable (zip-omap-after
           tree-omap-becomes-tree-in-order)
  :disable tree-omap-of-zip-tree-after)
