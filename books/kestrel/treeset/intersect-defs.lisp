; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "join-defs")
(include-book "set-defs")
(include-book "split-defs")

(set-induction-depth-limit 0)

(local (include-book "intersect"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-intersect
  ((x binary-tree-p)
   (y binary-tree-p))
  (declare (xargs :type-prescription (or (consp (tree-intersect x y))
                                         (equal (tree-intersect x y) nil))))
  :parents (implementation)
  :short "Take the intersection of two treaps."
  :long
  (xdoc::topstring
   (xdoc::p
     "The result might not be a intersection if the input trees are not binary search
      trees."))
  (cond ((or (tree-emptyp x)
             (tree-emptyp y))
         nil)
        ((heap< (tree-head x)
                (tree-head y))
         (b* (((mv in left right)
               (tree-split (tree-head y) x))
              (left (tree-intersect left (tree-left y)))
              (right (tree-intersect right (tree-right y))))
           (if in
               (tree-node (tree-head y) left right)
             (tree-join-at (tree-head y) left right))))
        (t
          (b* (((mv in left right)
                (tree-split (tree-head x) y))
               (left (tree-intersect (tree-left x) left))
               (right (tree-intersect (tree-right x) right)))
            (if in
                (tree-node (tree-head x) left right)
              (tree-join-at (tree-head x) left right)))))
  :measure (+ (acl2-count x)
              (acl2-count y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binary-intersect
  ((x setp)
   (y setp))
  (tree-intersect (sfix x) (sfix y)))

(define intersect-macro-loop
  ((list true-listp))
  :guard (and (consp list)
              (consp (rest list)))
  (if (endp (rest (rest list)))
      (list 'binary-intersect
            (first list)
            (second list))
    (list 'binary-intersect
          (first list)
          (intersect-macro-loop (rest list)))))

(defmacro intersect (x y &rest rst)
  (declare (xargs :guard t))
  (intersect-macro-loop (list* x y rst)))

(add-macro-fn intersect binary-intersect t)
