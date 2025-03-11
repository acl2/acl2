; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)

(include-book "binary-tree-defs")
(include-book "cardinality-defs")
(include-book "in-defs")
(include-book "set-defs")

(set-induction-depth-limit 0)

(local (include-book "join"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-join
  ((left binary-tree-p)
   (right binary-tree-p))
  :parents (implementation)
  :short "Join two trees which have previously been @(see tree-split)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Technically it is not required that the two trees are a result of a
      previous split call. It is only expected that, given a join @('(tree-join
      left right)'), there exists some @('x') such that @('(bst<-all-l left x)')
      and @('(bst<-all-r x right)'), as is produced by @('split')."))
  (cond ((tree-emptyp left)
         (tree-fix right))
        ((tree-emptyp right)
         (tree-fix left))
        ((heap< (tree-head left)
                (tree-head right))
         (tree-node (tree-head right)
                    (tree-join left (tree-left right))
                    (tree-right right)))
        (t (tree-node (tree-head left)
                      (tree-left left)
                      (tree-join (tree-right left) right))))
  :measure (+ (acl2-count left)
              (acl2-count right)))

(define tree-join-at
  (split
   (left binary-tree-p)
   (right binary-tree-p))
  (declare (ignore split))
  :parents (implementation)
  :short "Wrapper around @(tsee tree-join) annotated with a split point."
  :long
  (xdoc::topstring
   (xdoc::p
     "This @('split') argument is the value such that:")
   (xdoc::codeblock
     "(and (bst<-all-l left split)"
     "     (bst<-all-r split right))")
   (xdoc::p
     "While the @('split') argument is not used by the function, it is
      convenient to have so various rewriting rules can bind the variable
      appropriately without requiring @(':use') hints."))
  (tree-join left right)
  :no-function t
  :inline t)
