; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)

(include-book "cardinality-defs")
(include-book "in-defs")
(include-book "rotate-defs")
(include-book "set-defs")

(set-induction-depth-limit 0)

(local (include-book "insert"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-insert
  (x
   (tree binary-tree-p))
  :parents (implementation)
  :short "Insert a value into the tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "The element is inserted with respect to the binary search tree ordering
      and then rebalanced with respect to the @(tsee heapp) property."))
  (b* (((when (tree-emptyp tree))
        (tree-node x nil nil))
       ((when (equal x (tree-head tree)))
        (tree-fix tree))
       (lt (bst< x (tree-head tree))))
    (if lt
        (b* ((left$ (tree-insert x (tree-left tree)))
             (tree$ (tree-node-with-hint (tree-head tree)
                                         left$
                                         (tree-right tree)
                                         tree)))
          (if (heap< (tree-head tree)
                  (tree-head left$))
              (rotate-right tree$)
            tree$))
      (b* ((right$ (tree-insert x (tree-right tree)))
           (tree$ (tree-node-with-hint (tree-head tree)
                                       (tree-left tree)
                                       right$
                                       tree)))
        (if (heap< (tree-head tree)
                (tree-head right$))
            (rotate-left tree$)
          tree$)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert1
  (x
   (set setp))
  (tree-insert x (sfix set)))

(define insert-macro-loop
  ((list true-listp))
  :guard (and (consp list)
              (consp (rest list)))
  (if (endp (rest (rest list)))
      (list 'insert1
            (first list)
            (second list))
    (list 'insert1
          (first list)
          (insert-macro-loop (rest list)))))

(defmacro insert (x y &rest rst)
  (declare (xargs :guard t))
  (insert-macro-loop (list* x y rst)))

(add-macro-fn insert insert1 t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert-all
  ((list true-listp)
   (set setp))
  :parents (insert)
  :short "Add a list of values to the set."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n\\log(n+m))$), where @($n$) is the size of the list,
      and @($m$) is the size of the set."))
  (if (endp list)
      (sfix set)
    (insert-all (rest list)
                (insert (first list) set))))

(define from-list
  ((list true-listp))
  :parents (set)
  :short "Create a set from a list of values."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is just a wrapper around @(tsee insert-all).")
   (xdoc::p
     "Time complexity: @($O(n\\log(n))$)."))
  (insert-all list nil))
