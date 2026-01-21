; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
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

(include-book "std/basic/two-nats-measure" :dir :system)

(include-book "sum-acl2-count")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "kestrel/lists-light/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ binary-tree
  :parents (implementation)
  :short "Definition of a binary tree data structure."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binary-tree-p (x)
  (declare (xargs :type-prescription (booleanp (binary-tree-p x))))
  :short "Recognizer for @(see binary-tree)s."
  (or (null x)
      (and (consp x)
           (consp (cdr x))
           (binary-tree-p (cadr x))
           (binary-tree-p (cddr x))))
  :hints (("Goal" :in-theory (enable o< o-finp))))

(defrule binary-tree-p-compound-recognizer
  (if (binary-tree-p tree)
      (or (consp tree)
          (equal tree nil))
    (not (equal tree nil)))
  :rule-classes :compound-recognizer
  :enable binary-tree-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-fix ((tree binary-tree-p))
  :returns (tree$ binary-tree-p)
  :short "Fixer for @(see binary-tree)s."
  (mbe :logic (if (binary-tree-p tree) tree nil)
       :exec (the (or cons null) tree))
  :inline t)

(defrule tree-fix-when-binary-tree-p
  (implies (binary-tree-p tree)
           (equal (tree-fix tree)
                  tree))
  :enable tree-fix)

(defruled tree-fix-when-not-binary-tree-p
  (implies (not (binary-tree-p tree))
           (equal (tree-fix tree)
                  nil))
  :enable tree-fix)

(defrule tree-fix-when-not-binary-tree-p-cheap
  (implies (not (binary-tree-p tree))
           (equal (tree-fix tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-fix-when-not-binary-tree-p)

(defrule acl2-count-of-tree-fix-linear
  (<= (acl2-count (tree-fix tree))
      (acl2-count tree))
  :rule-classes :linear
  :enable tree-fix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-equiv
  ((x binary-tree-p)
   (y binary-tree-p))
  (declare (xargs :type-prescription (booleanp (tree-equiv x y))))
  :short "Equivalence up to @(tsee tree-fix)."
  (equal (tree-fix x)
         (tree-fix y))
  :inline t

  ///
  (defequiv tree-equiv))

(defrule tree-fix-under-tree-equiv
  (tree-equiv (tree-fix tree)
                     tree)
  :enable (tree-equiv
           tree-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-emptyp ((tree binary-tree-p))
  (declare (xargs :type-prescription (booleanp (tree-emptyp tree))))
  :short "Check if a @(see binary-tree) is empty."
  (endp (tree-fix tree))
  :inline t)

(defrule tree-emptyp-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (tree-emptyp x)
                  (tree-emptyp y)))
  :rule-classes :congruence
  :enable (tree-emptyp
           tree-equiv))

(defruled tree-fix-when-tree-emptyp
  (implies (tree-emptyp tree)
           (equal (tree-fix tree)
                  nil))
  :enable tree-emptyp)

(defrule tree-fix-when-tree-emptyp-cheap
  (implies (tree-emptyp tree)
           (equal (tree-fix tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-fix-when-tree-emptyp)

(defrule binary-tree-p-when-not-tree-emptyp-forward-chaining
  (implies (not (tree-emptyp tree))
           (binary-tree-p tree))
  :rule-classes :forward-chaining
  :enable tree-emptyp)

(defrule tree-emptyp-when-not-binary-tree-p-forward-chaining
  (implies (not (binary-tree-p tree))
           (tree-emptyp tree))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-head ((tree binary-tree-p))
  :short "Get the root element of the nonempty @(see binary-tree)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, returns @('nil')."))
  (car (tree-fix tree))
  :inline t)

(defrule tree-head-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (tree-head x)
                  (tree-head y)))
  :rule-classes :congruence
  :enable (tree-head
           tree-equiv))

(defruled tree-head-when-tree-emptyp
  (implies (tree-emptyp tree)
           (equal (tree-head tree)
                  nil))
  :enable tree-head)

(defrule tree-head-when-tree-emptyp-cheap
  (implies (tree-emptyp tree)
           (equal (tree-head tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-head-when-tree-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-left ((tree binary-tree-p))
  :returns (left binary-tree-p
                 :hints (("Goal" :in-theory (enable tree-fix
                                                    binary-tree-p))))
  :short "Get the left subtree of the nonempty @(see binary-tree)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, returns @('nil')."))
  (cadr (tree-fix tree))
  :guard-hints (("Goal" :in-theory (enable binary-tree-p)))
  :inline t)

(defrule tree-left-type-prescription
  (binary-tree-p (tree-left tree))
  :rule-classes ((:type-prescription :typed-term (tree-left tree))))

(defruled tree-left-when-tree-emptyp
  (implies (tree-emptyp tree)
           (equal (tree-left tree)
                  nil))
  :enable tree-left)

(defrule tree-left-when-tree-emptyp-cheap
  (implies (tree-emptyp tree)
           (equal (tree-left tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-left-when-tree-emptyp)

(defrule tree-emptyp-when-not-tree-emptyp-of-tree-left-forward-chaining
  (implies (not (tree-emptyp (tree-left tree)))
           (not (tree-emptyp tree)))
  :rule-classes :forward-chaining)

(defrule equal-of-tree-left-of-arg2-when-binary-tree-p
  ;; TODO: Does this trigger on the symmetric equality form? I think so.
  (implies (binary-tree-p x)
           (equal (equal (tree-left x) x)
                  (tree-emptyp x)))
  :enable (tree-left
           tree-emptyp
           tree-fix))

(defrule acl2-count-of-tree-left-linear
  (<= (acl2-count (tree-left tree))
      (acl2-count tree))
  :rule-classes :linear
  :enable (tree-emptyp
           tree-left
           tree-fix
           acl2-count
           fix))

(defrule acl2-count-of-tree-left-when-not-tree-emptyp-linear
  (implies (not (tree-emptyp tree))
           (< (acl2-count (tree-left tree))
              (acl2-count tree)))
  :rule-classes :linear
  :enable (tree-emptyp
           tree-fix
           tree-left
           acl2-count
           fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-right ((tree binary-tree-p))
  :returns (right binary-tree-p
                  :hints (("Goal" :in-theory (enable tree-fix
                                                     binary-tree-p))))
  :short "Get the right subtree of the nonempty @(see binary-tree)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, returns @('nil')."))
  (cddr (tree-fix tree))
  :guard-hints (("Goal" :in-theory (enable binary-tree-p)))
  :inline t)

(defrule tree-right-type-prescription
  (binary-tree-p (tree-right tree))
  :rule-classes ((:type-prescription :typed-term (tree-right tree))))

(defruled tree-right-when-tree-emptyp
  (implies (tree-emptyp tree)
           (equal (tree-right tree)
                  nil))
  :enable tree-right)

(defrule tree-right-when-tree-emptyp-cheap
  (implies (tree-emptyp tree)
           (equal (tree-right tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-right-when-tree-emptyp)

(defrule tree-emptyp-when-not-tree-emptyp-of-tree-right-forward-chaining
  (implies (not (tree-emptyp (tree-right tree)))
           (not (tree-emptyp tree)))
  :rule-classes :forward-chaining)

(defrule equal-of-tree-right-of-arg2-when-binary-tree-p
  ;; TODO: Does this trigger on the symmetric equality form? I think so.
  (implies (binary-tree-p x)
           (equal (equal (tree-right x) x)
                  (tree-emptyp x)))
  :enable (tree-right
           tree-emptyp
           tree-fix))

(defrule acl2-count-of-tree-right-linear
  (<= (acl2-count (tree-right tree))
      (acl2-count tree))
  :rule-classes :linear
  :enable (tree-emptyp
           tree-right
           tree-fix
           acl2-count
           fix))

(defrule acl2-count-of-tree-right-when-not-tree-emptyp-linear
  (implies (not (tree-emptyp tree))
           (< (acl2-count (tree-right tree))
              (acl2-count tree)))
  :rule-classes :linear
  :enable (tree-emptyp
           tree-fix
           tree-right
           acl2-count
           fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled acl2-count-when-binary-tree-p
  (implies (binary-tree-p tree)
           (equal (acl2-count tree)
                  (if (tree-emptyp tree)
                      0
                    (+ 2
                       (acl2-count (tree-head tree))
                       (acl2-count (tree-left tree))
                       (acl2-count (tree-right tree))))))
  :enable (acl2-count
           binary-tree-p
           tree-head
           tree-left
           tree-right
           tree-emptyp
           tree-fix))

(defrule acl2-count-when-not-tree-emptyp-cheap
  (implies (not (tree-emptyp tree))
           (equal (acl2-count tree)
                  (+ 2
                     (acl2-count (tree-head tree))
                     (acl2-count (tree-left tree))
                     (acl2-count (tree-right tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :use acl2-count-when-binary-tree-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-node
  (head
   (left binary-tree-p)
   (right binary-tree-p))
  (declare (xargs :type-prescription (consp (tree-node head left right))))
  :returns (tree binary-tree-p
                :hints (("Goal" :in-theory (enable binary-tree-p))))
  :short "Construct a nonempty @(see binary-tree)."
  (list* head
         (tree-fix left)
         (tree-fix right))
  :inline t)

(defrule tree-node-elim
  (implies (not (tree-emptyp tree))
           (equal (tree-node (tree-head tree)
                             (tree-left tree)
                             (tree-right tree))
                  tree))
  :rule-classes :elim
  :enable (tree-emptyp
           tree-node
           binary-tree-p
           tree-fix
           tree-head
           tree-left
           tree-right))

(defrule tree-head-of-tree-node
  (equal (tree-head (tree-node head left right))
         head)
  :enable (tree-node
           tree-head
           binary-tree-p))

(defrule tree-left-of-tree-node
  (equal (tree-left (tree-node head left right))
         (tree-fix left))
  :enable (tree-node
           tree-left
           binary-tree-p))

(defrule tree-right-of-tree-node
  (equal (tree-right (tree-node head left right))
         (tree-fix right))
  :enable (tree-node
           tree-right
           binary-tree-p))

(defrule tree-emptyp-of-tree-node
  (not (tree-emptyp (tree-node head left right)))
  :enable (tree-emptyp
           tree-node
           binary-tree-p))

(defrule acl2-count-of-tree-node
  (equal (acl2-count (tree-node head left right))
         (+ 2
            (acl2-count head)
            (acl2-count (tree-fix left))
            (acl2-count (tree-fix right))))
  :enable (tree-node
           acl2-count))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-node-with-hint
  (head
   (left binary-tree-p)
   (right binary-tree-p)
   (hint binary-tree-p))
  (declare (xargs :type-prescription
                  (consp (tree-node-with-hint head left right hint))))
  :returns (tree binary-tree-p
                :hints (("Goal" :in-theory (enable binary-tree-p))))
  :short "A variant of @(tsee tree-node) which uses @(tsee cons-with-hint)."
  (cons-with-hint
   head
   (cons-with-hint
     (tree-fix left)
     (tree-fix right)
     (cdr hint))
   hint)
  :inline t)

(defrule tree-node-with-hint-becomes-tree-node
  (equal (tree-node-with-hint head left right hint)
         (tree-node head left right))
  :enable (tree-node-with-hint
           tree-node))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-induct (tree)
  :short "Induct over the structure of a binary tree."
  (or (tree-emptyp tree)
      (let ((left (tree-induct (tree-left tree)))
            (right (tree-induct (tree-right tree))))
        (declare (ignore left right))
        t))
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards nil)

(in-theory (enable (:i tree-induct)))

(defruled tree-induction
  t
  :rule-classes
  ((:induction :pattern (binary-tree-p tree)
               :scheme (tree-induct tree))))

(defruled nonempty-tree-induction
  t
  :rule-classes
  ((:induction :pattern (not (tree-emptyp tree))
               :scheme (tree-induct tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binary-tree-listp (x)
  (declare (xargs :type-prescription (booleanp (binary-tree-listp x))))
  :short "Recognizer for a true list of binary trees."
  (if (consp x)
      (and (binary-tree-p (first x))
           (binary-tree-listp (rest x)))
    (null x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule binary-tree-listp-compound-recognizer
  (implies (binary-tree-listp trees)
           (true-listp trees))
  :rule-classes :compound-recognizer
  :induct t
  :enable binary-tree-listp)

(defrule binary-tree-p-of-car-when-binary-tree-listp
  (implies (binary-tree-listp trees)
           (binary-tree-p (car trees)))
  :enable binary-tree-listp)

(defrule binary-tree-listp-of-cdr-when-binary-tree-listp
  (implies (binary-tree-listp trees)
           (binary-tree-listp (cdr trees)))
  :enable binary-tree-listp)

(defrule binary-tree-listp-of-cons
  (equal (binary-tree-listp (cons x y))
         (and (binary-tree-p x)
              (binary-tree-listp y)))
  :enable binary-tree-listp)

;; TODO: other list theorems

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: are these useful?

(defruled equal-when-not-tree-emptyp-of-arg1
  (implies (not (tree-emptyp x))
           (equal (equal x y)
                  (and (not (tree-emptyp y))
                       (equal (tree-head x) (tree-head y))
                       (equal (tree-left x) (tree-left y))
                       (equal (tree-right x) (tree-right y))))))

(defruled equal-when-not-tree-emptyp-of-arg2
  (implies (not (tree-emptyp y))
           (equal (equal x y)
                  (and (not (tree-emptyp x))
                       (equal (tree-head x) (tree-head y))
                       (equal (tree-left x) (tree-left y))
                       (equal (tree-right x) (tree-right y))))))

(defruled equal-when-not-tree-emptyp-of-arg1-cheap
  (implies (not (tree-emptyp x))
           (equal (equal x y)
                  (and (not (tree-emptyp y))
                       (equal (tree-head x) (tree-head y))
                       (equal (tree-left x) (tree-left y))
                       (equal (tree-right x) (tree-right y)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defruled equal-when-not-tree-emptyp-of-arg2-cheap
  (implies (not (tree-emptyp y))
           (equal (equal x y)
                  (and (not (tree-emptyp x))
                       (equal (tree-head x) (tree-head y))
                       (equal (tree-left x) (tree-left y))
                       (equal (tree-right x) (tree-right y)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: a faster, tail-recursive implementation
(define tree-pre-order
  ((tree binary-tree-p))
  :returns (list true-listp)
  :short "Create a pre-order list of values from a tree."
  (if (tree-emptyp tree)
      nil
    (cons (tree-head tree)
          (append (tree-pre-order (tree-left tree))
                  (tree-pre-order (tree-right tree)))))
  :hints (("Goal" :in-theory (enable o< o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: a faster, tail-recursive implementation
(define tree-in-order
  ((tree binary-tree-p))
  :returns (list true-listp)
  :short "Create an in-order list of values from a tree."
  (if (tree-emptyp tree)
      nil
    (append (tree-in-order (tree-left tree))
            (cons (tree-head tree)
                  (tree-in-order (tree-right tree)))))
  :hints (("Goal" :in-theory (enable o< o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: a faster, tail-recursive implementation
(define tree-post-order
  ((tree binary-tree-p))
  :returns (list true-listp)
  :short "Create a post-order list of values from a tree."
  (if (tree-emptyp tree)
      nil
    (append (tree-pre-order (tree-left tree))
            (append (tree-post-order (tree-right tree))
                    (list (tree-head tree)))))
  :hints (("Goal" :in-theory (enable o< o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy binary-tree-extra-rules
  '(tree-fix-when-not-binary-tree-p
    tree-fix-when-tree-emptyp
    tree-head-when-tree-emptyp
    tree-left-when-tree-emptyp
    tree-right-when-tree-emptyp
    tree-induction
    nonempty-tree-induction))
