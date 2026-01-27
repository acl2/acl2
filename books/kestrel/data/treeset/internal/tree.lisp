; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)

(include-book "../hash-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/fixed-size-words/u32" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/lists-light/len" :dir :system))

(local (include-book "../hash"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ tree
  :parents (implementation)
  :short "Definition of a tagged binary tree data structure."
  :long
  (xdoc::topstring
    (xdoc::p
      "This captures the structure of @(see treeset)s, without the
       invariants."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tagged-element-p (x)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Recognizer for a hash-tagged element."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is a @(tsee cons) pair, where the @(tsee car) is the @(tsee hash) of
      the @(tsee cdr)."))
  (and (consp x)
       (let ((hash (car x)))
         (and (unsigned-byte-p 32 hash)
              (data::u32-equal hash (hash (cdr x))))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tagged-element-p)))

(defrule tagged-element-p-compound-recognizer
  (implies (tagged-element-p x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable tagged-element-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-tagged-element ()
  :returns (elem tagged-element-p)
  (cons (hash nil) nil))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t irr-tagged-element) (:e irr-tagged-element)))

(defrule irr-tagged-element-type-prescription
  (tagged-element-p (irr-tagged-element))
  :rule-classes ((:type-prescription :typed-term (irr-tagged-element))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tagged-element-fix ((elem tagged-element-p))
  :returns (elem$ tagged-element-p)
  :short "Fixer for @(see tagged-element-p)s."
  (mbe :logic (if (tagged-element-p elem) elem (irr-tagged-element))
       :exec (the cons elem))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tagged-element-p)))

(defrule tagged-element-fix-type-prescription
  (tagged-element-p (tagged-element-fix elem))
  :rule-classes ((:type-prescription :typed-term (tagged-element-fix elem))))

(defrule tagged-element-fix-when-tagged-element-p
  (implies (tagged-element-p elem)
           (equal (tagged-element-fix elem)
                  elem))
  :enable tagged-element-fix)

(defruled tagged-element-fix-when-not-tagged-element-p
  (implies (not (tagged-element-p elem))
           (equal (tagged-element-fix elem)
                  (irr-tagged-element)))
  :enable tagged-element-fix)

(defrule tagged-element-fix-when-not-tagged-element-p-cheap
  (implies (not (tagged-element-p elem))
           (equal (tagged-element-fix elem)
                  (irr-tagged-element)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tagged-element-fix-when-not-tagged-element-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tagged-element-equiv
  ((x tagged-element-p)
   (y tagged-element-p))
  :short "Equivalence up to @(tsee tagged-element-fix)."
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (equal (tagged-element-fix x)
         (tagged-element-fix y))
  :inline t

  ///
  (defequiv tagged-element-equiv))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tagged-element-equiv)))

(defrule tagged-element-fix-when-tagged-element-equiv-congruence
  (implies (tagged-element-equiv elem0 elem1)
           (equal (tagged-element-fix elem0)
                  (tagged-element-fix elem1)))
  :rule-classes :congruence
  :enable tagged-element-equiv)

(defrule tagged-element-fix-under-tagged-element-equiv
  (tagged-element-equiv (tagged-element-fix elem)
                        elem)
  :enable tagged-element-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tagged-element->elem ((elem tagged-element-p))
  (cdr (tagged-element-fix elem))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule tagged-element->elem-when-tagged-element-equiv-congruence
  (implies (tagged-element-equiv elem0 elem1)
           (equal (tagged-element->elem elem0)
                  (tagged-element->elem elem1)))
  :rule-classes :congruence
  :enable (tagged-element->elem
           tagged-element-equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tagged-element->hash ((elem tagged-element-p))
  :returns (hash (unsigned-byte-p 32 hash))
  (mbe :logic (hash (tagged-element->elem elem))
       :exec (car elem))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable tagged-element-p
                                           tagged-element->elem
                                           data::u32-equal))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tagged-element->hash)))

(defrule tagged-element->hash-type-prescription
  (natp (tagged-element->hash elem))
  :rule-classes :type-prescription)

(defrule tagged-element->hash-when-tagged-element-equiv-congruence
  (implies (tagged-element-equiv elem0 elem1)
           (equal (tagged-element->hash elem0)
                  (tagged-element->hash elem1)))
  :rule-classes :congruence
  :enable (tagged-element-equiv
           tagged-element->elem))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tagged-element
  ((hash (unsigned-byte-p 32 hash))
   x)
  :guard (mbe :logic (equal (hash x) hash)
              :exec (data::u32-equal (hash x) hash))
  :returns (elem tagged-element-p
                 :hints (("Goal" :in-theory (enable tagged-element-p))))
  :short "Constructor for @(tsee tagged-element-p)s."
  (cons (mbe :logic (hash x)
             :exec hash)
        x)
  :inline t
  :guard-hints (("Goal" :in-theory (enable data::u32-equal))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tagged-element)))

(defrule tagged-element-type-prescription
  (tagged-element-p (tagged-element hash x))
  :rule-classes ((:type-prescription :typed-term (tagged-element hash x))))

(defrule tagged-element-when-u32-equiv-congruence
  (implies (data::u32-equal hash0 hash1)
           (equal (tagged-element hash0 x)
                  (tagged-element hash1 x)))
  :rule-classes :congruence
  :enable tagged-element)

;; Logically, the first argument is ignored. We choose to arbitrarily normalize
;; it to nil.
(defruled tagged-element-arg1-becomes-nil
  (equal (tagged-element hash x)
         (tagged-element nil x))
  :enable tagged-element)

(defrule tagged-element-when-arg1-not-nil-syntaxp
  (implies (syntaxp (not (equal hash ''nil)))
           (equal (tagged-element hash x)
                  (tagged-element nil x)))
  :by tagged-element-arg1-becomes-nil)

(defrule tagged-element->elem-of-tagged-element
  (equal (tagged-element->elem (tagged-element hash x))
         x)
  :enable (tagged-element
           tagged-element->elem
           tagged-element-fix
           tagged-element-p))

(defrule tagged-element->hash-of-tagged-element
  (equal (tagged-element->hash (tagged-element hash x))
         (hash x))
  :enable (tagged-element
           tagged-element->elem
           tagged-element-fix
           tagged-element-p))

(defrule tagged-element-elim
  (implies (tagged-element-p elem)
           (equal (tagged-element (tagged-element->hash elem)
                                  (tagged-element->elem elem))
                  elem))
  :rule-classes :elim
  :enable (tagged-element
           tagged-element->hash
           tagged-element->elem
           tagged-element-p
           data::u32-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tagged-element$ (x)
  :returns (elem tagged-element-p)
  (tagged-element (hash x) x)
  :enabled t
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define treep (x)
  (declare (xargs :type-prescription (booleanp (treep x))))
  :short "Recognizer for @(see tree)s."
  (if (consp x)
      (and (tagged-element-p (car x))
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
     "For empty trees, this is logically @(tsee irr-tagged-element).")
   (xdoc::p
     "For a tree recognized by @(tsee heapp) (including @(see treeset)s), this
      is the largest element with respect to the @(tsee heap<) ordering. More
      precisely, it is the pair of the element along with its hash.
      @(tsee head) will project out just the element."))
  :guard (not (tree-empty-p tree))
  :returns (elem tagged-element-p
                 :hints (("Goal" :in-theory (enable tree-empty-p
                                                    tree-fix
                                                    treep))))
  (mbe :logic (if (tree-empty-p tree)
                  (irr-tagged-element)
                (car tree))
       :exec (car tree))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-empty-p
                                           treep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree->head)))

(defrule tree->head-type-prescription
  (tagged-element-p (tree->head tree))
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
                  (irr-tagged-element)))
  :enable tree->head)

(defrule tree->head-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree->head tree)
                  (irr-tagged-element)))
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
  ((head tagged-element-p)
   (left treep)
   (right treep))
  (declare (xargs :type-prescription (consp (tree-node head left right))))
  :returns (tree treep
                :hints (("Goal" :in-theory (enable treep))))
  :short "Construct a nonempty @(see tree)."
  (cons (tagged-element-fix head)
        (cons (tree-fix left) (tree-fix right)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-node-when-tagged-element-equiv-congruence
  (implies (tagged-element-equiv head0 head1)
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
         (tagged-element-fix head))
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
            (acl2-count (tagged-element-fix head))
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

;; Equality variants

(define tree-all-acl2-numberp ((tree treep))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (tree-empty-p tree)
      (and (acl2-numberp (tagged-element->elem (tree->head tree)))
           (tree-all-acl2-numberp (tree->left tree))
           (tree-all-acl2-numberp (tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-all-acl2-numberp)))

(defrule tree-all-acl2-numberp-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-all-acl2-numberp tree0)
                  (tree-all-acl2-numberp tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-all-acl2-numberp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-all-symbolp ((tree treep))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (tree-empty-p tree)
      (and (symbolp (tagged-element->elem (tree->head tree)))
           (tree-all-symbolp (tree->left tree))
           (tree-all-symbolp (tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-all-symbolp)))

(defrule tree-all-symbolp-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-all-symbolp tree0)
                  (tree-all-symbolp tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-all-symbolp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-all-eqlablep ((tree treep))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (tree-empty-p tree)
      (and (eqlablep (tagged-element->elem (tree->head tree)))
           (tree-all-eqlablep (tree->left tree))
           (tree-all-eqlablep (tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-all-eqlablep)))

(defrule tree-all-eqlablep-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-all-eqlablep tree0)
                  (tree-all-eqlablep tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-all-eqlablep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: mbe-in some slightly more efficient functions which does the treep and
;; tree-all checks simultaneously.

(define acl2-number-treep (x)
  (and (treep x)
       (tree-all-acl2-numberp x))
  :enabled t)

(define symbol-treep (x)
  (and (treep x)
       (tree-all-symbolp x))
  :enabled t)

(define eqlable-treep (x)
  (and (treep x)
       (tree-all-eqlablep x))
  :enabled t)

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
