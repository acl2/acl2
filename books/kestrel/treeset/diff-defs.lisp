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

(local (include-book "diff"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-diff
  ((x binary-tree-p)
   (y binary-tree-p))
  :parents (implementation)
  :short "Take the difference of two treaps."
  (cond ((or (tree-emptyp x)
             (tree-emptyp y))
         (tree-fix x))
        ((heap< (tree-head x)
                (tree-head y))
         (b* (((mv - left right)
               (tree-split (tree-head y) x))
              (left (tree-diff left (tree-left y)))
              (right (tree-diff right (tree-right y))))
           (tree-join-at (tree-head y) left right)))
        (t
          (b* (((mv in left right)
                (tree-split (tree-head x) y))
               (left (tree-diff (tree-left x) left))
               (right (tree-diff (tree-right x) right)))
            (if (not in)
                (tree-node (tree-head x) left right)
              (tree-join-at (tree-head x) left right)))))
  :measure (+ (acl2-count x)
              (acl2-count y))
  :hints (("Goal" :in-theory (enable o-p o< o-finp)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define diff
  ((x setp)
   (y setp))
  :parents (set)
  :short "Set difference."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(n\\log(m/n))$) (where @($n < m$))."))
  (tree-diff (sfix x) (sfix y)))
