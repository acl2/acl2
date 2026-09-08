; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/treeset/internal/in-order-defs" :dir :system)
(include-book "kestrel/data/treeset/internal/bst-defs" :dir :system)
(include-book "kestrel/data/treeset/to-oset-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/utilities/omap-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "values-defs")
(include-book "rlookup-defs")
(include-book "min-max-defs")
(include-book "count-defs")
(include-book "update-defs")
(include-book "delete-defs")
(include-book "update-star-defs")
(include-book "restrict-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/omap" :dir :system))
(local (include-book "std/omaps/extensionality" :dir :system))
(local (include-book "std/omaps/delete" :dir :system))

(local (include-book "kestrel/data/treeset/internal/in-order" :dir :system))
(local (include-book "kestrel/data/treeset/internal/bst" :dir :system))
(local (include-book "kestrel/data/treeset/to-oset" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "keys"))
(local (include-book "lookup"))
(local (include-book "values"))
(local (include-book "rlookup"))
(local (include-book "min-max"))
(local (include-book "count"))
(local (include-book "update"))
(local (include-book "delete"))
(local (include-book "update-star"))
(local (include-book "restrict"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-in-order-acc
  ((tree treep)
   (acc alistp))
  (declare (xargs :type-prescription :none))
  :returns (alist alistp)
  (if (tree-empty-p tree)
      (mbe :logic (if (alistp acc) acc nil)
           :exec acc)
    (tree-in-order-acc
      (tree->left tree)
      (cons (tree-element->key+val (tree->head tree))
            (tree-in-order-acc (tree->right tree)
                               acc))))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable alistp))))

;;;;;;;;;;;;;;;;;;;;

(defruled true-listp-of-tree-in-order-acc
  (true-listp (tree-in-order-acc tree acc))
  :induct t
  :enable tree-in-order-acc)

(defrule tree-in-order-acc-type-prescription
  (true-listp (tree-in-order-acc tree acc))
  :rule-classes :type-prescription
  :by true-listp-of-tree-in-order-acc)

;; TODO: Why does this get stuck?
;; (defrule tree-in-order-acc-when-tree-equiv-congruence
;;   (implies (tree-equiv tree0 tree1)
;;            (equal (tree-in-order-acc tree0 acc)
;;                   (tree-in-order-acc tree1 acc)))
;;   :rule-classes :congruence
;;   :induct (tree-in-order-acc tree0 acc)
;;   :enable tree-in-order-acc
;;   :disable (tree-empty-p-when-treep-cheap
;;             treep-when-not-tree-empty-p-forward-chaining))

(defrule tree-in-order-acc-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-in-order-acc tree0 acc)
                  (tree-in-order-acc tree1 acc)))
  :rule-classes :congruence
  :induct t
  :hints ('(:expand ((tree-in-order-acc tree0 acc)
                     (tree-in-order-acc tree1 acc))))
  :enable ((:i tree-in-order-acc)))

(defrule tree-in-order-acc-of-append
  (implies (and (alistp x)
                (alistp y))
           (equal (tree-in-order-acc tree (append x y))
                  (append (tree-in-order-acc tree x)
                          y)))
  :induct t
  :enable tree-in-order-acc)

(defruled tree-in-order-acc-arg2-becomes-nil
  (implies (alistp acc)
           (equal (tree-in-order-acc tree acc)
                  (append (tree-in-order-acc tree nil)
                          acc)))
  :use (:instance tree-in-order-acc-of-append
                  (x nil)
                  (y acc))
  :disable tree-in-order-acc-of-append)

(defruled tree-in-order-acc-arg2-becomes-nil-syntaxp
  (implies (and (syntaxp (not (equal acc ''nil)))
                (alistp acc))
           (equal (tree-in-order-acc tree acc)
                  (append (tree-in-order-acc tree nil)
                          acc)))
  :by tree-in-order-acc-arg2-becomes-nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-in-order
  ((tree treep))
  (declare (xargs :type-prescription :none))
  :returns (alist alistp)
  :parents (implementation)
  :short "Create an in-order alist of key-value pairs from a tree."
  (mbe :logic (if (tree-empty-p tree)
                  nil
                (append (tree-in-order (tree->left tree))
                        (cons (tree-element->key+val (tree->head tree))
                              (tree-in-order (tree->right tree)))))
       :exec (tree-in-order-acc tree nil))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defruled true-listp-of-tree-in-order
  (true-listp (tree-in-order tree))
  :induct t
  :enable tree-in-order)

(defrule tree-in-order-type-prescription
  (true-listp (tree-in-order tree))
  :rule-classes :type-prescription
  :by true-listp-of-tree-in-order)

(defrule tree-in-order-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-in-order tree0)
                  (tree-in-order tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-in-order)

(defrule tree-in-order-acc-becomes-tree-in-order
  (implies (alistp acc)
           (equal (tree-in-order-acc tree acc)
                  (append (tree-in-order tree)
                          acc)))
  :induct t
  :enable (tree-in-order
           tree-in-order-acc
           tree-in-order-acc-arg2-becomes-nil-syntaxp))

(verify-guards tree-in-order
  :hints (("Goal" :in-theory (enable tree-in-order))))

(defrule consp-of-tree-in-order
  (equal (consp (tree-in-order tree))
         (and (tree-in-order tree) t)))

(defrule tree-in-order-under-iff
  (iff (tree-in-order tree)
       (not (tree-empty-p tree)))
  :induct t
  :enable tree-in-order)

(defrule car-of-tree-in-order
  (equal (car (tree-in-order tree))
         (if (tree-empty-p tree)
             nil
           (tree-leftmost tree)))
  :induct t
  :expand ((tree-in-order tree))
  :enable tree-leftmost)

(defrule car-of-last-of-tree-in-order
  (equal (car (last (tree-in-order tree)))
         (if (tree-empty-p tree)
             nil
           (tree-rightmost tree)))
  :induct t
  :expand ((tree-in-order tree))
  :enable tree-rightmost)

(defruled tree-in-order-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree-in-order tree)
                  nil))
  :enable tree-in-order)

(defrule tree-in-order-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree-in-order tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-in-order-when-tree-empty-p)

(defrule len-of-tree-in-order
  (equal (len (tree-in-order tree))
         (tree-nodes-count tree))
  :induct t
  :enable (tree-in-order
           tree-nodes-count))

(defruled assoc-equal-of-tree-in-order-under-iff
  (iff (assoc-equal x (tree-in-order tree))
       (treeset::in x (tree-key-set tree)))
  :induct t
  :enable tree-in-order)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled assoc-equal-of-tree-in-order
  (equal (assoc-equal key (tree-in-order tree))
         (if (tree-empty-p tree)
             nil
           (or (assoc-equal key (tree-in-order (tree->left tree)))
               (and (equal (tree-element->key (tree->head tree)) key)
                    (tree-element->key+val (tree->head tree)))
               (assoc-equal key (tree-in-order (tree->right tree))))))
  :induct t
  :enable tree-in-order)

(defrule assoc-equal-of-tree-in-order-when-bstp
  (implies (bstp tree)
           (equal (assoc-equal key (tree-in-order tree))
                  (if (treeset::in key (tree-key-set tree))
                      (cons key (tree-lookup key tree))
                    nil)))
  :induct t
  :enable tree-in-order)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule omapp-of-tree-in-order-when-bstp
  (implies (bstp tree)
           (omap::mapp (tree-in-order tree)))
  :induct t
  :enable (tree-in-order
           data::omap-from-alist))

;;;;;;;;;;;;;;;;;;;;

(defrule assoc-of-tree-in-order-when-bstp
  (implies (bstp tree)
           (equal (omap::assoc key (tree-in-order tree))
                  (if (treeset::in key (tree-key-set tree))
                      (cons key (tree-lookup key tree))
                    nil)))
  :enable data::omap-assoc-becomes-assoc-equal)

(defrule size-of-tree-in-order-when-bstp
  (implies (bstp tree)
           (equal (omap::size (tree-in-order tree))
                  (tree-nodes-count tree)))
  :enable data::size-becomes-len-when-omapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule keys-of-tree-in-order
  (implies (bstp tree)
           (equal (omap::keys (tree-in-order tree))
                  (treeset::to-oset (tree-key-set tree))))
  :enable (set::expensive-rules
           omap::in-of-keys-to-assoc))

(defrule values-of-tree-in-order
  (implies (bstp tree)
           (equal (omap::values (tree-in-order tree))
                  (treeset::to-oset (tree-val-set tree))))
  :enable (set::expensive-rules
           data::omap-values-becomes-strip-cdrs)
  :prep-lemmas
  ((defrule member-equal-of-strip-cdrs-tree-in-order-under-iff
     (iff (member-equal val (strip-cdrs (tree-in-order tree)))
          (treeset::in val (tree-val-set tree)))
     :induct t
     :enable (tree-val-set
              tree-in-order
              member-equal))))

(defrule rlookup-of-tree-in-order
  (implies (bstp tree)
           (equal (omap::rlookup val (tree-in-order tree))
                  (treeset::to-oset (tree-rlookup val tree))))
  :enable set::expensive-rules)

(defrule tree-in-order-of-tree-update
  (implies (bstp tree)
           (equal (tree-in-order (tree-update key hash val tree))
                  (omap::update key val (tree-in-order tree))))
  :enable (omap::equal-becomes-ext-equal-when-mapp
           omap::ext-equal))

(defrule tree-in-order-of-tree-delete
  (implies (bstp tree)
           (equal (tree-in-order (tree-delete key tree))
                  (omap::delete key (tree-in-order tree))))
  :enable (omap::equal-becomes-ext-equal-when-mapp
           omap::ext-equal))

(defrule tree-in-order-of-tree-update*
  (implies (and (bstp x)
                (bstp y))
           (equal (tree-in-order (tree-update* x y))
                  (omap::update* (tree-in-order x)
                                 (tree-in-order y))))
  :enable (omap::equal-becomes-ext-equal-when-mapp
           omap::ext-equal))

(defrule tree-in-order-of-tree-restrict
  (implies (and (treeset::bstp keys)
                (bstp tree))
           (equal (tree-in-order (tree-restrict keys tree))
                  (omap::restrict (treeset::tree-in-order keys)
                                  (tree-in-order tree))))
  :enable (omap::equal-becomes-ext-equal-when-mapp
           omap::ext-equal
           omap::assoc-of-restrict))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-omap ((tree treep))
  :returns (omap omap::mapp)
  :verify-guards :after-returns
  :parents (implementation)
  :short "The entries of a tree, as an omap."
  :long
  (xdoc::topstring
   (xdoc::p
     "Built with omap primitives, so the result is an @(tsee omap::mapp)
      structurally, for any tree at all. Over a binary search tree this agrees
      with @(tsee tree-in-order), which builds the same omap in @($O(n)$) by
      reading the entries off in order; see
      @('tree-omap-becomes-tree-in-order'). This function is the logical form:
      definitions phrased over it face the mature omap theory rather than
      facts about alists.")
   (xdoc::p
     "The head's binding is applied outermost, and so wins over both subtrees.
      Over a search tree no key repeats, so the precedence is not observable;
      it only settles what the fold means on a malformed tree. This mirrors
      @('tree-key-set'), which inserts the head's key over the union of the
      two subtrees' key sets."))
  (if (tree-empty-p tree)
      nil
    (omap::update (tree-element->key (tree->head tree))
                  (tree-element->val (tree->head tree))
                  (omap::update* (tree-omap (tree->left tree))
                                 (tree-omap (tree->right tree))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-omap) (:e tree-omap)))

(defrule tree-omap-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-omap tree0)
                  (tree-omap tree1)))
  :rule-classes :congruence
  :expand ((tree-omap tree0)
           (tree-omap tree1)))

;; A key is bound exactly when it is a key of the tree, with no hypothesis:
;; the fold binds exactly the keys of the tree, ordered or not. This is the
;; mirror of `in-of-tree-oset' in TREESET, and holds for the same reason --
;; both folds put the head over the two subtrees.
;;
;; The two sides live in different set representations: `omap::keys' yields an
;; oset, while `tree-key-set' is a treeset. So the fact is stated as
;; membership rather than as an equality of sets, which is also the form
;; `in-of-tree-oset' takes.

(defrule assoc-of-tree-omap-under-iff
  (iff (omap::assoc key (tree-omap tree))
       (treeset::in key (tree-key-set tree)))
  :induct t
  :enable tree-omap)

(defrule omap-emptyp-of-tree-omap
  (equal (omap::emptyp (tree-omap tree))
         (tree-empty-p tree))
  :expand ((tree-omap tree)))

;; Over a search tree the fold binds each of its keys to the tree's lookup,
;; the same characterization `assoc-of-tree-in-order-when-bstp' gives the
;; alist builder. The hypothesis is needed for the values, not the keys: it is
;; what rules out a key appearing in both subtrees, where the fold's
;; precedence and the lookup's descent could disagree.

(defrule assoc-of-tree-omap-when-bstp
  (implies (bstp tree)
           (equal (omap::assoc key (tree-omap tree))
                  (if (treeset::in key (tree-key-set tree))
                      (cons key (tree-lookup key tree))
                    nil)))
  :induct t
  :enable tree-omap)

;;;;;;;;;;;;;;;;;;;;

;; Over a binary search tree the two builders agree exactly: both produce
;; omaps, and they bind the same keys to the same values.

(defruled tree-omap-becomes-tree-in-order
  (implies (bstp tree)
           (equal (tree-omap tree)
                  (tree-in-order tree)))
  :enable (omap::equal-becomes-ext-equal-when-mapp
           omap::ext-equal))
