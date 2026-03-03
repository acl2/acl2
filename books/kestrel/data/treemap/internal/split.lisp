; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "tree-defs")
(include-book "rotate-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "submap-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "keys"))
(local (include-book "lookup"))
(local (include-book "rotate"))
(local (include-book "submap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-split
  (key
   (tree treep))
  :parents (implementation)
  :short "Split a tree into two disjoint subtrees."
  :long
  (xdoc::topstring
   (xdoc::p
     "When @('tree') is a @('map'), @('(tree-split key tree)') yields
      @('(mv in left right)') where:")
   (xdoc::ul
     (xdoc::li "@('assoc') is an optional pair representing
                @('(tree-search-assoc key tree)').")
     (xdoc::li "@('left') is a @('map') containing all keys of @('tree') less
                than @('key') (with respect to @('<<')).")
     (xdoc::li "@('right') is a @('map') containing all keys of @('tree')
                greater than @('key') (with respect to @('<<'))."))
   (xdoc::p
     "The implementation is comparable to @('tree-update') if we were to
      pretend @('key') is maximal with respect to @('heap<')."))
  :returns (mv assoc
               (left treep)
               (right treep))
  (cond ((tree-empty-p tree)
         (mv nil nil nil))
        ((equal key (tree-element->key (tree->head tree)))
         (mv (tree-element->key+val (tree->head tree))
             (tree->left tree)
             (tree->right tree)))
        ((<< key (tree-element->key (tree->head tree)))
         (mv-let (assoc left$ right$)
                 (tree-split key (tree->left tree))
           (mbe :logic (let ((tree$ (rotate-right
                                      (tree-node (tree->head tree)
                                                 (tree-node key left$ right$)
                                                 (tree->right tree)))))
                         (mv assoc (tree->left tree$) (tree->right tree$)))
                ;; TODO: not clear this isn't simpler than the :logic branch
                ;; Also not clear whether the compiler couldn't just make this
                ;;   simplification (since rotate is inlined).
                :exec (mv assoc
                          left$
                          (tree-node (tree->head tree)
                                     right$
                                     (tree->right tree))))))
        (t
         (mv-let (assoc left$ right$)
                 (tree-split key (tree->right tree))
           (mbe :logic (let ((tree$ (rotate-left
                                      (tree-node (tree->head tree)
                                                 (tree->left tree)
                                                 (tree-node key left$ right$)))))
                         (mv assoc (tree->left tree$) (tree->right tree$)))
                :exec (mv assoc
                          (tree-node (tree->head tree)
                                     (tree->left tree)
                                     left$)
                          right$)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-split.assoc-when-type-prescription
  (or (consp (mv-nth 0 (tree-split key tree)))
      (equal (mv-nth 0 (tree-split key tree)) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-split)

(defrule tree-split.left-when-type-prescription
  (or (consp (mv-nth 1 (tree-split key tree)))
      (equal (mv-nth 1 (tree-split key tree)) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-split)

(defrule tree-split.right-when-type-prescription
  (or (consp (mv-nth 2 (tree-split key tree)))
      (equal (mv-nth 2 (tree-split key tree)) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-split)

(defrule tree-split-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-split key tree0)
                  (tree-split key tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-split.in-when-tree-empty-p
  (implies (tree-empty-p tree)
           (not (mv-nth 0 (tree-split key tree))))
  :enable tree-split)

(defrule tree-split.in-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (not (mv-nth 0 (tree-split key tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-split.in-when-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-empty-p-of-tree-split.left-when-tree-empty-p
  (implies (tree-empty-p tree)
           (tree-empty-p (mv-nth 1 (tree-split key tree))))
  :enable tree-split)

(defrule tree-empty-p-of-tree-split.left-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (tree-empty-p (mv-nth 1 (tree-split key tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-empty-p-of-tree-split.left-when-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-empty-p-of-tree-split.right-when-tree-empty-p
  (implies (tree-empty-p tree)
           (tree-empty-p (mv-nth 2 (tree-split key tree))))
  :enable tree-split)

(defrule tree-empty-p-of-tree-split.right-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (tree-empty-p (mv-nth 2 (tree-split key tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-empty-p-of-tree-split.right-when-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-split.assoc-when-bstp
  (equal (mv-nth 0 (tree-split key tree))
         (tree-search-assoc key tree))
  :induct t
  :enable (tree-split
           tree-search-assoc))

;;;;;;;;;;;;;;;;;;;;

(defruled <<-all-l-of-tree-split.left-when-<<-all-l
  (implies (<<-all-l tree y)
           (<<-all-l (mv-nth 1 (tree-split x tree)) y))
  :induct t
  :enable tree-split)

(defrule <<-all-l-of-tree-split.left-when-<<-all-l-cheap
  (implies (<<-all-l tree y)
           (<<-all-l (mv-nth 1 (tree-split x tree)) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by <<-all-l-of-tree-split.left-when-<<-all-l)

;;;;;;;;;;;;;;;;;;;;

(defruled <<-all-l-of-tree-split.right-when-<<-all-l
  (implies (<<-all-l tree y)
           (<<-all-l (mv-nth 2 (tree-split x tree)) y))
  :induct t
  :enable tree-split)

(defrule <<-all-l-of-tree-split.right-when-<<-all-l-cheap
  (implies (<<-all-l tree y)
           (<<-all-l (mv-nth 2 (tree-split x tree)) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by <<-all-l-of-tree-split.right-when-<<-all-l)

;;;;;;;;;;;;;;;;;;;;

(defruled <<-all-r-of-arg1-and-tree-split.left-when-<<-all-r
  (implies (<<-all-r x tree)
           (<<-all-r x (mv-nth 1 (tree-split y tree))))
  :induct t
  :enable tree-split)

(defrule <<-all-r-of-arg1-and-tree-split.left-when-<<-all-r-cheap
  (implies (<<-all-r x tree)
           (<<-all-r x (mv-nth 1 (tree-split y tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by <<-all-r-of-arg1-and-tree-split.left-when-<<-all-r)

;;;;;;;;;;;;;;;;;;;;

(defruled <<-all-r-of-arg1-and-tree-split.right-when-<<-all-r
  (implies (<<-all-r x tree)
           (<<-all-r x (mv-nth 2 (tree-split y tree))))
  :induct t
  :enable tree-split)

(defrule <<-all-r-of-arg1-and-tree-split.right-when-<<-all-r-cheap
  (implies (<<-all-r x tree)
           (<<-all-r x (mv-nth 2 (tree-split y tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by <<-all-r-of-arg1-and-tree-split.right-when-<<-all-r)

;;;;;;;;;;;;;;;;;;;;

(defruled <<-all-l-when-<<-all-l-of-tree-split.left-and-tree-split.right
  (implies (and (<<-all-l (mv-nth 1 (tree-split x tree)) y)
                (<<-all-l (mv-nth 2 (tree-split x tree)) y)
                (<< x y))
           (<<-all-l tree y))
  :induct t
  :enable tree-split)

(defruled <<-all-r-when-<<-all-l-of-arg1-and-tree-split.left-and-tree-split.right
  (implies (and (<<-all-r x (mv-nth 1 (tree-split y tree)))
                (<<-all-r x (mv-nth 2 (tree-split y tree)))
                (<< x y))
           (<<-all-r x tree))
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-tree-split.left-when-bstp
  (implies (bstp tree)
           (bstp (mv-nth 1 (tree-split key tree))))
  :induct t
  :enable (tree-split
           bstp))

(defrule bstp-of-tree-split.right-when-bstp
  (implies (bstp tree)
           (bstp (mv-nth 2 (tree-split key tree))))
  :induct t
  :enable (tree-split
           bstp))

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-split.left-of-arg1-and-arg1
  (implies (bstp tree)
           (<<-all-l (mv-nth 1 (tree-split key tree)) key))
  :induct t
  :enable (tree-split
           bstp
           <<-all-extra-rules
           data::<<-rules))

(defrule <<-all-r-of-arg1-and-tree-split.right-of-arg1
  (implies (bstp tree)
           (<<-all-r key (mv-nth 2 (tree-split key tree))))
  :induct t
  :enable (tree-split
           bstp
           <<-all-extra-rules
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defruled heap<-all-l-of-tree-split.left-when-heap<-all-l
  (implies (heap<-all-l tree y)
           (heap<-all-l (mv-nth 1 (tree-split x tree)) y))
  :induct t
  :enable tree-split)

(defrule heap<-all-l-of-tree-split.left-when-heap<-all-l-cheap
  (implies (heap<-all-l tree y)
           (heap<-all-l (mv-nth 1 (tree-split x tree)) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable heap<-all-l-of-tree-split.left-when-heap<-all-l)

;;;;;;;;;;;;;;;;;;;;

(defruled heap<-all-l-of-tree-split.right-when-heap<-all-l
  (implies (heap<-all-l tree y)
           (heap<-all-l (mv-nth 2 (tree-split x tree)) y))
  :induct t
  :enable tree-split)

(defrule heap<-all-l-of-tree-split.right-when-heap<-all-l-cheap
  (implies (heap<-all-l tree y)
           (heap<-all-l (mv-nth 2 (tree-split x tree)) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable heap<-all-l-of-tree-split.right-when-heap<-all-l)

;;;;;;;;;;;;;;;;;;;;

(defruled heap<-all-l-when-heap<-all-l-of-tree-split.left-and-tree-split.right
  (implies (and (heap<-all-l (mv-nth 1 (tree-split x tree)) y)
                (heap<-all-l (mv-nth 2 (tree-split x tree)) y)
                (heap< x y))
           (heap<-all-l tree y))
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-split.left-when-heapp
  (implies (heapp tree)
           (heapp (mv-nth 1 (tree-split key tree))))
  :induct t
  :enable tree-split)

(defrule heapp-of-tree-split.right-when-heapp
  (implies (heapp tree)
           (heapp (mv-nth 2 (tree-split key tree))))
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled in-of-tree-key-set-when-in-of-tree-key-set-tree-split.left
  (implies (treeset::in x (tree-key-set (mv-nth 1 (tree-split y tree))))
           (treeset::in x (tree-key-set tree)))
  :induct t
  :enable (tree-split
           tree-key-set))

(defruled subset-of-tree-key-set-and-tree-key-set-tree-split.left
  (treeset::subset (tree-key-set (mv-nth 1 (tree-split y tree)))
                   (tree-key-set tree))
  :enable (treeset::pick-a-point
           in-of-tree-key-set-when-in-of-tree-key-set-tree-split.left))

;; (defrule tree-in-when-tree-in-of-tree-split.left-forward-chaining
;;   (implies (tree-in x (mv-nth 1 (tree-split y tree)))
;;            (tree-in x tree))
;;   :rule-classes :forward-chaining
;;   :enable tree-in-when-tree-in-of-tree-split.left)

(defrule subset-of-tree-key-set-and-tree-key-set-tree-split.left-forward-chaining
  (treeset::subset (tree-key-set (mv-nth 1 (tree-split y tree)))
                   (tree-key-set tree))
  :rule-classes ((:forward-chaining :trigger-terms ((tree-split y tree))))
  :by subset-of-tree-key-set-and-tree-key-set-tree-split.left)

;;;;;;;;;;;;;;;;;;;;

(defruled in-of-tree-key-set-when-in-of-tree-key-set-tree-split.right
  (implies (treeset::in x (tree-key-set (mv-nth 2 (tree-split y tree))))
           (treeset::in x (tree-key-set tree)))
  :induct t
  :enable (tree-split
           tree-key-set))

(defruled subset-of-tree-key-set-and-tree-key-set-tree-split.right
  (treeset::subset (tree-key-set (mv-nth 2 (tree-split y tree)))
                   (tree-key-set tree))
  :enable (treeset::pick-a-point
           in-of-tree-key-set-when-in-of-tree-key-set-tree-split.right))

;; (defrule tree-in-when-tree-in-of-tree-split.right-forward-chaining
;;   (implies (tree-in x (mv-nth 2 (tree-split y tree)))
;;            (tree-in x tree))
;;   :rule-classes :forward-chaining
;;   :enable tree-in-when-tree-in-of-tree-split.right)

(defrule subset-of-tree-key-set-and-tree-key-set-tree-split.right-forward-chaining
  (treeset::subset (tree-key-set (mv-nth 2 (tree-split y tree)))
                   (tree-key-set tree))
  :rule-classes ((:forward-chaining :trigger-terms ((tree-split y tree))))
  :by subset-of-tree-key-set-and-tree-key-set-tree-split.right)

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree-key-set-tree-split.left
  (implies (bstp tree)
           (equal (treeset::in x (tree-key-set (mv-nth 1 (tree-split y tree))))
                  (and (treeset::in x (tree-key-set tree))
                       (<< x y))))
  :induct t
  :enable (tree-split
           tree-key-set
           data::<<-rules
           bstp))

(defrule in-of-tree-key-set-tree-split.right
  (implies (bstp tree)
           (equal (treeset::in x (tree-key-set (mv-nth 2 (tree-split y tree))))
                  (and (treeset::in x (tree-key-set tree))
                       (<< y x))))
  :induct t
  :enable (tree-split
           tree-key-set
           data::<<-rules
           bstp))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-lookup-of-tree-split.left
  (implies (bstp tree)
           (equal (tree-lookup x (mv-nth 1 (tree-split y tree)))
                  (if (<< x y)
                      (tree-lookup x tree)
                    nil)))
  :induct t
  :enable (tree-split
           data::<<-rules))

(defrule tree-lookup-of-tree-split.right
  (implies (bstp tree)
           (equal (tree-lookup x (mv-nth 2 (tree-split y tree)))
                  (if (<< y x)
                      (tree-lookup x tree)
                    nil)))
  :induct t
  :enable (tree-split
           data::<<-expensive-rules))

;;;;;;;;;;;;;;;;;;;;

(defruled <<-all-r-when-tree-empty-p-of-tree-split.left
  (implies (and (bstp tree)
                (<< x y)
                (tree-empty-p (mv-nth 1 (tree-split y tree))))
           (<<-all-r x tree))
  :induct t
  :enable (tree-split
           data::<<-rules
           <<-all-extra-rules))

;; TODO: is this a reasonable rule?
(defrule <<-all-r-when-tree-empty-p-of-tree-split.left-forward-chaining
  (implies (and (tree-empty-p (mv-nth 1 (tree-split y tree)))
                (<< x y)
                (bstp tree))
           (<<-all-r x tree))
  :rule-classes :forward-chaining
  :by <<-all-r-when-tree-empty-p-of-tree-split.left)

;;;;;;;;;;;;;;;;;;;;

(defruled <<-all-l-when-tree-empty-p-of-tree-split.right
  (implies (and (bstp tree)
                (<< y x)
                (tree-empty-p (mv-nth 2 (tree-split y tree))))
           (<<-all-l tree x))
  :induct t
  :enable (tree-split
           <<-all-extra-rules)
  :prep-lemmas
  ((defrule lemma0
     (implies (and (not (<< y (tree-element->key (tree->head tree))))
                   (<<-all-l (tree->right tree) x)
                   (bstp tree)
                   (<< y x))
              (<<-all-l tree x))
     :enable (data::<<-expensive-rules
              <<-all-extra-rules))))

;; TODO: is this a reasonable rule?
(defrule <<-all-l-when-tree-empty-p-of-tree-split.right-forward-chaining
  (implies (and (tree-empty-p (mv-nth 2 (tree-split y tree)))
                (<< y x)
                (bstp tree))
           (<<-all-l tree x))
  :rule-classes :forward-chaining
  :by <<-all-l-when-tree-empty-p-of-tree-split.right)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-of-tree-split.left-when-<<-all-r
  (implies (<<-all-r key tree)
           (tree-empty-p (mv-nth 1 (tree-split key tree))))
  :induct t
  :enable tree-split)

(defrule tree-empty-p-of-tree-split.right-when-<<-all-r
  (implies (<<-all-l tree key)
           (tree-empty-p (mv-nth 2 (tree-split key tree))))
  :induct t
  :enable (tree-split
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule acl2-count-of-tree-split.left-linear
  (implies (treep tree)
           (<= (acl2-count (mv-nth 1 (tree-split key tree)))
               (acl2-count tree)))
  :rule-classes :linear
  :induct t
  :enable tree-split)

(defrule acl2-count-of-tree-split.right-linear
  (<= (acl2-count (mv-nth 2 (tree-split key tree)))
      (acl2-count tree))
  :rule-classes :linear
  :induct t
  :enable tree-split)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-split-of-tree->head
  (equal (tree-split (tree-element->key (tree->head tree)) tree)
         (mv (if (tree-empty-p tree)
                 nil
               (tree-element->key+val (tree->head tree)))
             (tree->left tree)
             (tree->right tree)))
  :enable tree-split)

(defrule tree-split-of-bind-tree->head-cheap
  (implies (equal x (tree-element->key (tree->head tree)))
           (equal (tree-split x tree)
                  (mv (if (tree-empty-p tree)
                          nil
                        (tree-element->key+val (tree->head tree)))
                      (tree->left tree)
                      (tree->right tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :use tree-split-of-tree->head
  :disable tree-split-of-tree->head)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: unused?

(defrule tree-keys-acl2-numberp-of-tree-split.left
  (implies (tree-keys-acl2-numberp tree)
           (tree-keys-acl2-numberp (mv-nth 1 (tree-split x tree))))
  :induct t
  :enable (tree-split
           tree-keys-acl2-numberp))

(defrule tree-keys-acl2-numberp-of-tree-split.right
  (implies (tree-keys-acl2-numberp tree)
           (tree-keys-acl2-numberp (mv-nth 2 (tree-split x tree))))
  :induct t
  :enable (tree-split
           tree-keys-acl2-numberp))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-keys-symbolp-of-tree-split.left
  (implies (tree-keys-symbolp tree)
           (tree-keys-symbolp (mv-nth 1 (tree-split x tree))))
  :induct t
  :enable (tree-split
           tree-keys-symbolp))

(defrule tree-keys-symbolp-of-tree-split.right
  (implies (tree-keys-symbolp tree)
           (tree-keys-symbolp (mv-nth 2 (tree-split x tree))))
  :induct t
  :enable (tree-split
           tree-keys-symbolp))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-keys-eqlablep-of-tree-split.left
  (implies (tree-keys-eqlablep tree)
           (tree-keys-eqlablep (mv-nth 1 (tree-split x tree))))
  :induct t
  :enable (tree-split
           tree-keys-eqlablep))

(defrule tree-keys-eqlablep-of-tree-split.right
  (implies (tree-keys-eqlablep tree)
           (tree-keys-eqlablep (mv-nth 2 (tree-split x tree))))
  :induct t
  :enable (tree-split
           tree-keys-eqlablep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-split
  ((key acl2-numberp)
   (tree acl2-number-treep))
  (mbe :logic (tree-split key tree)
       :exec
       (cond ((tree-empty-p tree)
              (mv nil nil nil))
             ((= key (tree-element->key (tree->head tree)))
              (mv (tree-element->key+val (tree->head tree))
                  (tree->left tree)
                  (tree->right tree)))
             ((data::acl2-number-<< key (tree-element->key (tree->head tree)))
              (mv-let (assoc left$ right$)
                      (acl2-number-tree-split key (tree->left tree))
                (mv assoc
                    left$
                    (tree-node (tree->head tree)
                               right$
                               (tree->right tree)))))
             (t
              (mv-let (assoc left$ right$)
                      (acl2-number-tree-split key (tree->right tree))
                (mv assoc
                    (tree-node (tree->head tree)
                               (tree->left tree)
                               left$)
                    right$)))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-split
                                           acl2-number-tree-split
                                           tree-keys-acl2-numberp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-split
  ((key symbolp)
   (tree symbol-treep))
  (mbe :logic (tree-split key tree)
       :exec
       (cond ((tree-empty-p tree)
              (mv nil nil nil))
             ((eq key (tree-element->key (tree->head tree)))
              (mv (tree-element->key+val (tree->head tree))
                  (tree->left tree)
                  (tree->right tree)))
             ((data::symbol-<< key (tree-element->key (tree->head tree)))
              (mv-let (assoc left$ right$)
                      (symbol-tree-split key (tree->left tree))
                (mv assoc
                    left$
                    (tree-node (tree->head tree)
                               right$
                               (tree->right tree)))))
             (t
              (mv-let (assoc left$ right$)
                      (symbol-tree-split key (tree->right tree))
                (mv assoc
                    (tree-node (tree->head tree)
                               (tree->left tree)
                               left$)
                    right$)))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-split
                                           symbol-tree-split
                                           tree-keys-symbolp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-split
  ((key eqlablep)
   (tree eqlable-treep))
  (mbe :logic (tree-split key tree)
       :exec
       (cond ((tree-empty-p tree)
              (mv nil nil nil))
             ((eql key (tree-element->key (tree->head tree)))
              (mv (tree-element->key+val (tree->head tree))
                  (tree->left tree)
                  (tree->right tree)))
             ((data::eqlable-<< key (tree-element->key (tree->head tree)))
              (mv-let (assoc left$ right$)
                      (eqlable-tree-split key (tree->left tree))
                (mv assoc
                    left$
                    (tree-node (tree->head tree)
                               right$
                               (tree->right tree)))))
             (t
              (mv-let (assoc left$ right$)
                      (eqlable-tree-split key (tree->right tree))
                (mv assoc
                    (tree-node (tree->head tree)
                               (tree->left tree)
                               left$)
                    right$)))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-split
                                           eqlable-tree-split
                                           tree-keys-eqlablep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy tree-split-extra-rules
  '(tree-split.in-when-tree-empty-p
    tree-empty-p-of-tree-split.left-when-tree-empty-p
    tree-empty-p-of-tree-split.right-when-tree-empty-p
    <<-all-l-of-tree-split.left-when-<<-all-l
    <<-all-l-of-tree-split.right-when-<<-all-l
    <<-all-r-of-arg1-and-tree-split.left-when-<<-all-r
    <<-all-r-of-arg1-and-tree-split.right-when-<<-all-r
    <<-all-l-when-<<-all-l-of-tree-split.left-and-tree-split.right
    <<-all-r-when-<<-all-l-of-arg1-and-tree-split.left-and-tree-split.right
    heap<-all-l-of-tree-split.left-when-heap<-all-l
    heap<-all-l-of-tree-split.right-when-heap<-all-l
    heap<-all-l-when-heap<-all-l-of-tree-split.left-and-tree-split.right
    in-of-tree-key-set-when-in-of-tree-key-set-tree-split.left
    subset-of-tree-key-set-and-tree-key-set-tree-split.left
    in-of-tree-key-set-when-in-of-tree-key-set-tree-split.right
    subset-of-tree-key-set-and-tree-key-set-tree-split.right))
