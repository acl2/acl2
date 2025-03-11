; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "set-defs")
(include-book "split-defs")

(set-induction-depth-limit 0)

(local (include-book "union"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-union
  ((x binary-tree-p)
   (y binary-tree-p))
  :parents (implementation)
  :short "Take the union of two treaps."
  :long
  (xdoc::topstring
   (xdoc::p
     "The result might not be a union if the input trees are not binary search
      trees."))
  :returns (tree binary-tree-p)
  (cond ((tree-emptyp x)
         (tree-fix y))
        ((tree-emptyp y)
         (tree-fix x))
        ((heap< (tree-head x)
             (tree-head y))
         (b* (((mv - left right)
               (tree-split (tree-head y) x)))
           (tree-node (tree-head y)
                      (tree-union left (tree-left y))
                      (tree-union right (tree-right y)))))
        (t (b* (((mv - left right)
                 (tree-split (tree-head x) y)))
             (tree-node (tree-head x)
                        (tree-union (tree-left x) left)
                        (tree-union (tree-right x) right)))))
  :measure (+ (acl2-count x)
              (acl2-count y))
  :hints (("Goal" :in-theory (enable o-p o< o-finp)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binary-union
  ((x setp)
   (y setp))
  (tree-union (sfix x) (sfix y)))

(define union-macro-loop
  ((list true-listp))
  :guard (and (consp list)
              (consp (rest list)))
  (if (endp (rest (rest list)))
      (list 'binary-union
            (first list)
            (second list))
    (list 'binary-union
          (first list)
          (union-macro-loop (rest list)))))

(defmacro union (x y &rest rst)
  (declare (xargs :guard t))
  (union-macro-loop (list* x y rst)))

(add-macro-fn union binary-union t)
