; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/topics" :dir :system)

(include-book "std/basic/two-nats-measure" :dir :system)

(set-induction-depth-limit 0)

(local (include-book "binary-tree"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binary-tree-p (x)
  (declare (xargs :type-prescription (booleanp (binary-tree-p x))))
  :short "Recognizer for @(see binary-tree)s."
  (or (null x)
      (and (consp x)
           (consp (cdr x))
           (binary-tree-p (cadr x))
           (binary-tree-p (cddr x)))))

(define tree-fix ((tree binary-tree-p))
  :short "Fixer for @(see binary-tree)s."
  (mbe :logic (if (binary-tree-p tree) tree nil)
       :exec (the (or cons null) tree))
  :no-function t
  :inline t)

(define tree-equiv
  ((x binary-tree-p)
   (y binary-tree-p))
  (declare (xargs :type-prescription (booleanp (tree-equiv x y))))
  :short "Equivalence up to @(tsee tree-fix)."
  (equal (tree-fix x)
         (tree-fix y))
  :no-function t
  :inline t)

(defequiv tree-equiv)

(define tree-emptyp ((tree binary-tree-p))
  (declare (xargs :type-prescription (booleanp (tree-emptyp tree))))
  :short "Check if a @(see binary-tree) is empty."
  (endp (tree-fix tree))
  :no-function t
  :inline t)

(define tree-head ((tree binary-tree-p))
  :short "Get the root element of the nonempty @(see binary-tree)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, returns @('nil')."))
  (car (tree-fix tree))
  :no-function t
  :inline t)

(define tree-left ((tree binary-tree-p))
  :short "Get the left subtree of the nonempty @(see binary-tree)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, returns @('nil')."))
  (cadr (tree-fix tree))
  :no-function t
  :inline t)

(define tree-right ((tree binary-tree-p))
  :short "Get the right subtree of the nonempty @(see binary-tree)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, returns @('nil')."))
  (cddr (tree-fix tree))
  :no-function t
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-node
  (head
   (left binary-tree-p)
   (right binary-tree-p))
  (declare (xargs :type-prescription (consp (tree-node head left right))))
  :short "Construct a nonempty @(see binary-tree)."
  (list* head
         (tree-fix left)
         (tree-fix right))
  :no-function t
  :inline t)

(define tree-node-with-hint
  (head
   (left binary-tree-p)
   (right binary-tree-p)
   (hint binary-tree-p))
  (declare (xargs :type-prescription
                  (consp (tree-node-with-hint head left right hint))))
  :short "A variant of @(tsee tree-node) which uses @(tsee cons-with-hint)."
  (cons-with-hint
   head
   (cons-with-hint
     (tree-fix left)
     (tree-fix right)
     (cdr hint))
   hint)
  :no-function t
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binary-tree-listp (x)
  (declare (xargs :type-prescription (booleanp (binary-tree-listp x))))
  :short "Recognizer for a true list of binary trees."
  (if (consp x)
      (and (binary-tree-p (first x))
           (binary-tree-listp (rest x)))
    (null x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-pre-order
  ((tree binary-tree-p))
  :short "Create a pre-order list of values from a tree."
  (if (tree-emptyp tree)
      nil
    (cons (tree-head tree)
          (append (tree-pre-order (tree-left tree))
                  (tree-pre-order (tree-right tree))))))

(define tree-in-order
  ((tree binary-tree-p))
  :short "Create an in-order list of values from a tree."
  (if (tree-emptyp tree)
      nil
    (append (tree-in-order (tree-left tree))
            (cons (tree-head tree)
                  (tree-in-order (tree-right tree))))))

(define tree-post-order
  ((tree binary-tree-p))
  :short "Create a post-order list of values from a tree."
  (if (tree-emptyp tree)
      nil
    (append (tree-pre-order (tree-left tree))
            (append (tree-post-order (tree-right tree))
                    (list (tree-head tree))))))
