; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "kestrel/data/treeset/hash-defs" :dir :system)
(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/hash" :dir :system))
(local (include-book "kestrel/data/utilities/fixed-size-words/u32" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/lists-light/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ tree
  :parents (implementation)
  :short "Definition of a binary tree data structure."
  :long
  (xdoc::topstring
    (xdoc::p
      "This captures the structure of @(see treemap)s, without the
       invariants."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: rename tree-element-p to tree-element-p in treeset/internal?
;; TODO: swap hash and key.
(define tree-element-p (x)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Recognizer for a tree element."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is a triple, containing a hash, a key, and value.
      The hash is the hash of the key."))
  (and (consp x)
       (consp (cdr x))
       (let ((hash (car x)))
         (and (unsigned-byte-p 32 hash)
              (data::u32-equal hash (hash (cadr x))))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-element-p)))

(defrule tree-element-p-compound-recognizer
  (implies (tree-element-p x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable tree-element-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-tree-element ()
  :returns (elem tree-element-p)
  (list* (hash nil) nil nil))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t irr-tree-element) (:e irr-tree-element)))

(defrule irr-tree-element-type-prescription
  (tree-element-p (irr-tree-element))
  :rule-classes ((:type-prescription :typed-term (irr-tree-element))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-element-fix ((elem tree-element-p))
  :returns (elem$ tree-element-p)
  :short "Fixer for @(see tree-element-p)s."
  (mbe :logic (if (tree-element-p elem) elem (irr-tree-element))
       :exec (the cons elem))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-element-p)))

(defrule tree-element-fix-type-prescription
  (tree-element-p (tree-element-fix elem))
  :rule-classes ((:type-prescription :typed-term (tree-element-fix elem))))

(defrule tree-element-fix-when-tree-element-p
  (implies (tree-element-p elem)
           (equal (tree-element-fix elem)
                  elem))
  :enable tree-element-fix)

(defruled tree-element-fix-when-not-tree-element-p
  (implies (not (tree-element-p elem))
           (equal (tree-element-fix elem)
                  (irr-tree-element)))
  :enable tree-element-fix)

(defrule tree-element-fix-when-not-tree-element-p-cheap
  (implies (not (tree-element-p elem))
           (equal (tree-element-fix elem)
                  (irr-tree-element)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-element-fix-when-not-tree-element-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-element-equiv
  ((x tree-element-p)
   (y tree-element-p))
  :short "Equivalence up to @(tsee tree-element-fix)."
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (equal (tree-element-fix x)
         (tree-element-fix y))
  :inline t

  ///
  (defequiv tree-element-equiv))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-element-equiv)))

(defrule tree-element-fix-when-tree-element-equiv-congruence
  (implies (tree-element-equiv elem0 elem1)
           (equal (tree-element-fix elem0)
                  (tree-element-fix elem1)))
  :rule-classes :congruence
  :enable tree-element-equiv)

(defrule tree-element-fix-under-tree-element-equiv
  (tree-element-equiv (tree-element-fix elem)
                        elem)
  :enable tree-element-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-element->key ((elem tree-element-p))
  (cadr (tree-element-fix elem))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-element-p))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-element->key-when-tree-element-equiv-congruence
  (implies (tree-element-equiv elem0 elem1)
           (equal (tree-element->key elem0)
                  (tree-element->key elem1)))
  :rule-classes :congruence
  :enable (tree-element->key
           tree-element-equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-element->val ((elem tree-element-p))
  (cddr (tree-element-fix elem))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-element-p))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-element->val-when-tree-element-equiv-congruence
  (implies (tree-element-equiv elem0 elem1)
           (equal (tree-element->val elem0)
                  (tree-element->val elem1)))
  :rule-classes :congruence
  :enable (tree-element->val
           tree-element-equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-element->hash ((elem tree-element-p))
  :returns (hash (unsigned-byte-p 32 hash))
  (mbe :logic (hash (tree-element->key elem))
       :exec (car elem))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-element-p
                                           tree-element->key
                                           data::u32-equal))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-element->hash)))

(defrule tree-element->hash-type-prescription
  (natp (tree-element->hash elem))
  :rule-classes :type-prescription)

(defrule tree-element->hash-when-tree-element-equiv-congruence
  (implies (tree-element-equiv elem0 elem1)
           (equal (tree-element->hash elem0)
                  (tree-element->hash elem1)))
  :rule-classes :congruence
  :enable tree-element->hash)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Where else should this be used. Assoc maybe?
(define tree-element->key+val ((elem tree-element-p))
  (mbe :logic (cons (tree-element->key elem)
                    (tree-element->val elem))
       :exec (cdr elem))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-element->key
                                           tree-element->val
                                           tree-element-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-element
  ((hash (unsigned-byte-p 32 hash))
   key
   val)
  :guard (mbe :logic (equal (hash key) hash)
              :exec (data::u32-equal (hash key) hash))
  :returns (elem tree-element-p
                 :hints (("Goal" :in-theory (enable tree-element-p))))
  :short "Constructor for @(tsee tree-element-p)s."
  (list* (mbe :logic (hash key)
              :exec hash)
         key
         val)
  :inline t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-element)))

(defrule tree-element-type-prescription
  (tree-element-p (tree-element hash key val))
  :rule-classes ((:type-prescription :typed-term (tree-element hash key val))))

(defrule tree-element-when-u32-equiv-congruence
  (implies (data::u32-equal hash0 hash1)
           (equal (tree-element hash0 key val)
                  (tree-element hash1 key val)))
  :rule-classes :congruence
  :enable tree-element)

;; Logically, the first argument is ignored. We choose to arbitrarily normalize
;; it to nil.
(defruled tree-element-arg1-becomes-nil
  (equal (tree-element hash key val)
         (tree-element nil key val))
  :enable tree-element)

(defrule tree-element-when-arg1-not-nil-syntaxp
  (implies (syntaxp (not (equal hash ''nil)))
           (equal (tree-element hash key val)
                  (tree-element nil key val)))
  :by tree-element-arg1-becomes-nil)

(defrule tree-element->key-of-tree-element
  (equal (tree-element->key (tree-element hash key val))
         key)
  :enable (tree-element
           tree-element->key
           tree-element-fix
           tree-element-p))

(defrule tree-element->val-of-tree-element
  (equal (tree-element->val (tree-element hash key val))
         val)
  :enable (tree-element
           tree-element->val
           tree-element-fix
           tree-element-p))

(defrule tree-element->hash-of-tree-element
  (equal (tree-element->hash (tree-element hash key val))
         (hash key))
  :enable tree-element->hash)

(defrule tree-element-elim
  (implies (tree-element-p elem)
           (equal (tree-element (tree-element->hash elem)
                                (tree-element->key elem)
                                (tree-element->val elem))
                  elem))
  :rule-classes :elim
  :enable (tree-element
           tree-element->hash
           tree-element->key
           tree-element->val
           tree-element-p
           data::u32-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-element$ (key val)
  :returns (elem tree-element-p)
  (tree-element (hash key) key val)
  :enabled t
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define treep (x)
  (declare (xargs :type-prescription (booleanp (treep x))))
  :short "Recognizer for @(see tree)s."
  (if (consp x)
      (and (tree-element-p (car x))
           (consp (cdr x))
           (treep (cadr x))
           (treep (cddr x)))
    (null x)))

;;;;;;;;;;;;;;;;;;;;

(defrule treep-compound-recognizer
  (if (treep tree)
      (or (consp tree)
          (equal tree nil))
    (not (equal tree nil)))
  :rule-classes :compound-recognizer
  :enable treep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-fix ((tree treep))
  :returns (tree$ treep)
  :short "Fixer for @(see tree)s."
  (mbe :logic (if (treep tree) tree nil)
       :exec (the list tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-fix)))

(defrule tree-fix-type-prescription
  (or (consp (tree-fix tree))
      (equal (tree-fix tree) nil))
  :rule-classes :type-prescription
  :enable tree-fix)

(defrule tree-fix-when-treep
  (implies (treep tree)
           (equal (tree-fix tree)
                  tree))
  :enable tree-fix)

(defruled tree-fix-when-not-treep
  (implies (not (treep tree))
           (equal (tree-fix tree)
                  nil))
  :enable tree-fix)

(defrule tree-fix-when-not-treep-cheap
  (implies (not (treep tree))
           (equal (tree-fix tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-fix-when-not-treep)

(defrule acl2-count-of-tree-fix-linear
  (<= (acl2-count (tree-fix tree))
      (acl2-count tree))
  :rule-classes :linear
  :enable tree-fix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-equiv
  ((x treep)
   (y treep))
  (declare (xargs :type-prescription (booleanp (tree-equiv x y))))
  :short "Equivalence up to @(tsee tree-fix)."
  (equal (tree-fix x)
         (tree-fix y))
  :inline t

  ///
  (defequiv tree-equiv))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-fix-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-fix tree0)
                  (tree-fix tree1)))
  :rule-classes :congruence
  :enable tree-equiv)

(defrule tree-fix-under-tree-equiv
  (tree-equiv (tree-fix tree)
              tree)
  :enable tree-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-empty-p ((tree treep))
  (declare (xargs :type-prescription (booleanp (tree-empty-p tree))))
  :short "Check if a @(see tree) is empty."
  (endp (tree-fix tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-empty-p tree0)
                  (tree-empty-p tree1)))
  :rule-classes :congruence
  :enable tree-empty-p)

(defrule tree-empty-p-compound-recognizer
  (implies (not (tree-empty-p tree))
           (consp tree))
  :rule-classes :compound-recognizer
  :enable (tree-empty-p
           tree-fix))

(defruled tree-empty-p-when-treep
  (implies (treep tree)
           (equal (tree-empty-p tree)
                  (equal tree nil)))
  :enable (tree-empty-p
           tree-fix))

(defrule tree-empty-p-when-treep-cheap
  (implies (treep tree)
           (equal (tree-empty-p tree)
                  (equal tree nil)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-empty-p-when-treep)

(defruled tree-fix-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree-fix tree)
                  nil))
  :enable tree-empty-p)

(defrule tree-fix-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree-fix tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-fix-when-tree-empty-p)

(defrule treep-when-not-tree-empty-p-forward-chaining
  (implies (not (tree-empty-p tree))
           (treep tree))
  :rule-classes :forward-chaining
  :enable tree-empty-p)

(defrule tree-empty-p-when-not-treep-forward-chaining
  (implies (not (treep tree))
           (tree-empty-p tree))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree->head ((tree treep))
  :short "Get the root element of the nonempty @(see tree)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, this is logically @(tsee irr-tree-element).")
   (xdoc::p
     "For a tree recognized by @(tsee heapp) (including @(see treeset)s), this
      is the largest element with respect to the @(tsee heap<) ordering. More
      precisely, it is the pair of the element along with its hash.
      @(tsee head) will project out just the element."))
  :guard (not (tree-empty-p tree))
  :returns (elem tree-element-p
                 :hints (("Goal" :in-theory (enable tree-empty-p
                                                    tree-fix
                                                    treep))))
  (mbe :logic (if (tree-empty-p tree)
                  (irr-tree-element)
                (car tree))
       :exec (car tree))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-empty-p
                                           treep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree->head)))

(defrule tree->head-type-prescription
  (tree-element-p (tree->head tree))
  :rule-classes ((:type-prescription :typed-term (tree->head tree))))

(defrule tree->head-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree->head tree0)
                  (tree->head tree1)))
  :rule-classes :congruence
  :enable (tree->head
           tree-equiv))

(defruled tree->head-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree->head tree)
                  (irr-tree-element)))
  :enable tree->head)

(defrule tree->head-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree->head tree)
                  (irr-tree-element)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree->head-when-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree->left ((tree treep))
  :short "Get the left subtree of the nonempty @(see tree)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, returns @('nil')."))
  :returns (left treep
                 :hints (("Goal" :in-theory (enable tree-fix
                                                    treep))))
  (cadr (tree-fix tree))
  :inline t
  :guard-hints (("Goal" :in-theory (enable treep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree->left)))

(defrule tree->left-type-prescription
  (treep (tree->left tree))
  :rule-classes ((:type-prescription :typed-term (tree->left tree))))

(defrule tree->left-when-tree-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree->left tree0)
                  (tree->left tree1)))
  :rule-classes :congruence
  :enable tree->left)

(defruled tree->left-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree->left tree)
                  nil))
  :enable tree->left)

(defrule tree->left-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree->left tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree->left-when-tree-empty-p)

(defrule tree-empty-p-when-not-tree-empty-p-of-tree->left-forward-chaining
  (implies (not (tree-empty-p (tree->left tree)))
           (not (tree-empty-p tree)))
  :rule-classes :forward-chaining)

(defrule equal-of-tree->left-of-arg2-when-treep
  ;; TODO: Does this trigger on the symmetric equality form? I think so.
  (implies (treep x)
           (equal (equal (tree->left x) x)
                  (tree-empty-p x)))
  :enable (tree->left
           tree-empty-p
           tree-fix))

(defrule acl2-count-of-tree->left-linear
  (<= (acl2-count (tree->left tree))
      (acl2-count tree))
  :rule-classes :linear
  :enable (tree-empty-p
           tree->left
           tree-fix
           acl2-count
           acl2::fix))

(defrule acl2-count-of-tree->left-when-not-tree-empty-p-linear
  (implies (not (tree-empty-p tree))
           (< (acl2-count (tree->left tree))
              (acl2-count tree)))
  :rule-classes :linear
  :enable (tree-empty-p
           tree-fix
           tree->left
           acl2-count
           acl2::fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree->right ((tree treep))
  :returns (right treep
                  :hints (("Goal" :in-theory (enable tree-fix
                                                     treep))))
  :short "Get the right subtree of the nonempty @(see tree)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, returns @('nil')."))
  (cddr (tree-fix tree))
  :inline t
  :guard-hints (("Goal" :in-theory (enable treep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree->right)))

(defrule tree->right-type-prescription
  (treep (tree->right tree))
  :rule-classes ((:type-prescription :typed-term (tree->right tree))))

(defrule tree->right-when-tree-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree->right tree0)
                  (tree->right tree1)))
  :rule-classes :congruence
  :enable tree->right)

(defruled tree->right-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree->right tree)
                  nil))
  :enable tree->right)

(defrule tree->right-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree->right tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree->right-when-tree-empty-p)

(defrule tree-empty-p-when-not-tree-empty-p-of-tree->right-forward-chaining
  (implies (not (tree-empty-p (tree->right tree)))
           (not (tree-empty-p tree)))
  :rule-classes :forward-chaining)

(defrule equal-of-tree->right-of-arg2-when-treep
  ;; TODO: Does this trigger on the symmetric equality form? I think so.
  (implies (treep x)
           (equal (equal (tree->right x) x)
                  (tree-empty-p x)))
  :enable (tree->right
           tree-empty-p
           tree-fix))

(defrule acl2-count-of-tree->right-linear
  (<= (acl2-count (tree->right tree))
      (acl2-count tree))
  :rule-classes :linear
  :enable (tree-empty-p
           tree->right
           tree-fix
           acl2-count
           acl2::fix))

(defrule acl2-count-of-tree->right-when-not-tree-empty-p-linear
  (implies (not (tree-empty-p tree))
           (< (acl2-count (tree->right tree))
              (acl2-count tree)))
  :rule-classes :linear
  :enable (tree-empty-p
           tree-fix
           tree->right
           acl2-count
           acl2::fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled acl2-count-when-treep
  (implies (treep tree)
           (equal (acl2-count tree)
                  (if (tree-empty-p tree)
                      0
                    (+ 2
                       (acl2-count (tree->head tree))
                       (acl2-count (tree->left tree))
                       (acl2-count (tree->right tree))))))
  :enable (acl2-count
           treep
           tree->head
           tree->left
           tree->right
           tree-empty-p
           tree-fix))

(defrule acl2-count-when-not-tree-empty-p-cheap
  (implies (not (tree-empty-p (double-rewrite tree)))
           (equal (acl2-count tree)
                  (+ 2
                     (acl2-count (tree->head (double-rewrite tree)))
                     (acl2-count (tree->left (double-rewrite tree)))
                     (acl2-count (tree->right (double-rewrite tree))))))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :use acl2-count-when-treep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-node
  ((head tree-element-p)
   (left treep)
   (right treep))
  (declare (xargs :type-prescription (consp (tree-node head left right))))
  :returns (tree treep
                :hints (("Goal" :in-theory (enable treep))))
  :short "Construct a nonempty @(see tree)."
  (cons (tree-element-fix head)
        (cons (tree-fix left) (tree-fix right)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-node-when-tree-element-equiv-congruence
  (implies (tree-element-equiv head0 head1)
           (equal (tree-node head0 left right)
                  (tree-node head1 left right)))
  :rule-classes :congruence
  :enable tree-node)

(defrule tree-node-when-tree-equiv-of-arg3-congruence
  (implies (tree-equiv left0 left1)
           (equal (tree-node head left0 right)
                  (tree-node head left1 right)))
  :rule-classes :congruence
  :enable tree-node)

(defrule tree-node-when-tree-equiv-of-arg4-congruence
  (implies (tree-equiv right0 right1)
           (equal (tree-node head left right0)
                  (tree-node head left right1)))
  :rule-classes :congruence
  :enable tree-node)

(defrule tree-node-elim
  (implies (not (tree-empty-p tree))
           (equal (tree-node (tree->head tree)
                             (tree->left tree)
                             (tree->right tree))
                  tree))
  :rule-classes :elim
  :enable (tree-empty-p
           tree-node
           treep
           tree-fix
           tree->head
           tree->left
           tree->right))

(defrule tree->head-of-tree-node
  (equal (tree->head (tree-node head left right))
         (tree-element-fix head))
  :enable (tree-node
           tree->head
           treep
           tree-empty-p))

(defrule tree->left-of-tree-node
  (equal (tree->left (tree-node head left right))
         (tree-fix left))
  :enable (tree-node
           tree->left
           treep))

(defrule tree->right-of-tree-node
  (equal (tree->right (tree-node head left right))
         (tree-fix right))
  :enable (tree-node
           tree->right
           treep))

(defrule tree-empty-p-of-tree-node
  (not (tree-empty-p (tree-node head left right)))
  :enable (tree-empty-p
           tree-node
           treep))

(defrule acl2-count-of-tree-node
  (equal (acl2-count (tree-node head left right))
         (+ 2
            (acl2-count (tree-element-fix head))
            (acl2-count (tree-fix left))
            (acl2-count (tree-fix right))))
  :enable (tree-node
           acl2-count))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-induct (tree)
  :short "Induct over the structure of a binary tree."
  (or (tree-empty-p tree)
      (let ((left (tree-induct (tree->left tree)))
            (right (tree-induct (tree->right tree))))
        (declare (ignore left right))
        nil))
  :verify-guards nil)

(in-theory (enable (:i tree-induct)))

(defruled tree-induction
  t
  :rule-classes
  ((:induction :pattern (treep tree)
               :scheme (tree-induct tree))))

(defruled nonempty-tree-induction
  t
  :rule-classes
  ((:induction :pattern (not (tree-empty-p tree))
               :scheme (tree-induct tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-bi-induct (x y)
  :short "Induct over the structure of two binary trees simultaneously."
  (or (tree-empty-p x)
      (tree-empty-p y)
      (let ((left (tree-bi-induct (tree->left x) (tree->left y)))
            (right (tree-bi-induct (tree->right x) (tree->right y))))
        (declare (ignore left right))
        nil))
  :verify-guards nil)

(in-theory (enable (:i tree-bi-induct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-listp (x)
  (declare (xargs :type-prescription (booleanp (tree-listp x))))
  :short "Recognizer for a true list of @(see tree)s."
  (if (consp x)
      (and (treep (first x))
           (tree-listp (rest x)))
    (null x)))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-listp-compound-recognizer
  (if (tree-listp trees)
      (true-listp trees)
    (not (equal trees nil)))
  :rule-classes :compound-recognizer
  :induct t
  :enable tree-listp)

(defrule treep-of-car-when-tree-listp
  (implies (tree-listp trees)
           (treep (car trees)))
  :enable tree-listp)

(defrule tree-listp-of-cdr-when-tree-listp
  (implies (tree-listp trees)
           (tree-listp (cdr trees)))
  :enable tree-listp)

(defrule tree-listp-of-cons
  (equal (tree-listp (cons x y))
         (and (treep x)
              (tree-listp y)))
  :enable tree-listp)

(defrule tree-listp-of-append
  (implies (tree-listp x)
           (equal (tree-listp (append x y))
                  (tree-listp y)))
  :induct t
  :enable (append
           tree-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-list-fix ((trees tree-listp))
  :returns (trees$ tree-listp)
  (mbe :logic (if (tree-listp trees)
                  trees
                nil)
       :exec trees)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-list-fix)))

(defrule tree-list-fix-type-prescription
  (true-listp (tree-list-fix trees))
  :rule-classes :type-prescription
  :enable tree-list-fix)

(defrule tree-list-fix-when-tree-listp
  (implies (tree-listp trees)
           (equal (tree-list-fix trees)
                  trees))
  :enable tree-list-fix)

(defruled tree-list-fix-when-not-tree-listp
  (implies (not (tree-listp trees))
           (equal (tree-list-fix trees)
                  nil))
  :enable tree-list-fix)

(defrule tree-list-fix-when-not-tree-listp-cheap
  (implies (not (tree-listp trees))
           (equal (tree-list-fix trees)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-list-fix-when-not-tree-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: are these useful?

(defruled equal-when-not-tree-empty-p-of-arg1
  (implies (not (tree-empty-p x))
           (equal (equal x y)
                  (and (not (tree-empty-p y))
                       (equal (tree->head x) (tree->head y))
                       (equal (tree->left x) (tree->left y))
                       (equal (tree->right x) (tree->right y))))))

(defruled equal-when-not-tree-empty-p-of-arg2
  (implies (not (tree-empty-p y))
           (equal (equal x y)
                  (and (not (tree-empty-p x))
                       (equal (tree->head x) (tree->head y))
                       (equal (tree->left x) (tree->left y))
                       (equal (tree->right x) (tree->right y))))))

(defruled equal-when-not-tree-empty-p-of-arg1-cheap
  (implies (not (tree-empty-p x))
           (equal (equal x y)
                  (and (not (tree-empty-p y))
                       (equal (tree->head x) (tree->head y))
                       (equal (tree->left x) (tree->left y))
                       (equal (tree->right x) (tree->right y)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defruled equal-when-not-tree-empty-p-of-arg2-cheap
  (implies (not (tree-empty-p y))
           (equal (equal x y)
                  (and (not (tree-empty-p x))
                       (equal (tree->head x) (tree->head y))
                       (equal (tree->left x) (tree->left y))
                       (equal (tree->right x) (tree->right y)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy tree-extra-rules
  '(tree-fix-when-not-treep
    tree-fix-when-tree-empty-p
    tree->head-when-tree-empty-p
    tree->left-when-tree-empty-p
    tree->right-when-tree-empty-p
    tree-induction
    nonempty-tree-induction
    ))
