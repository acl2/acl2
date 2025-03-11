; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "binary-tree-defs")
(include-book "rotate-defs")
(include-book "set-defs")

(set-induction-depth-limit 0)

(local (include-book "split"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-split
  (x
   (tree binary-tree-p))
  :parents (implementation)
  :short "Split a tree into two disjoint subtrees."
  :long
  (xdoc::topstring
   (xdoc::p
     "When @('tree') is a @('set'), @('(tree-split x tree)') yields
      @('(mv in left right)') where:")
   (xdoc::ul
     (xdoc::li "@('in') is a boolean representing @('(tree-in x tree)').")
     (xdoc::li "@('left') is a @('set') containing all elements of @('tree')
                less than @('x') (with respect to @('bst<')).")
     (xdoc::li "@('right') is a @('set') containing all elements of @('tree')
                greater than @('x') (with respect to @('bst<'))."))
   (xdoc::p
     "The implementation is comparable to @('tree-insert') if we were to
      pretend @('x') is maximal with respect to @('heap<')."))
  (b* (((when (tree-emptyp tree))
        (mv nil nil nil))
       ((when (equal x (tree-head tree)))
        (mv t (tree-left tree) (tree-right tree))))
    (if (bst< x (tree-head tree))
        (b* (;; Interpret as a tree-node (use x instead of in)
             ;; (may violate heapp)
             ((mv in left$ right$)
              (tree-split x (tree-left tree))))
          (mbe :logic (let ((tree$ (rotate-right
                                     (tree-node (tree-head tree)
                                                (tree-node x left$ right$)
                                                (tree-right tree)))))
                        (mv in (tree-left tree$) (tree-right tree$)))
               ;; TODO: not clear this isn't simpler than the :logic branch
               ;; Also not clear whether the compiler couldn't just make this
               ;;   simplification (since rotate is inlined).
               :exec (mv in
                         left$
                         (tree-node (tree-head tree)
                                    right$
                                    (tree-right tree)))))
      (b* (((mv in left$ right$)
            (tree-split x (tree-right tree))))
        (mbe :logic (let ((tree$ (rotate-left
                                   (tree-node (tree-head tree)
                                              (tree-left tree)
                                              (tree-node x left$ right$)))))
                      (mv in (tree-left tree$) (tree-right tree$)))
             :exec (mv in
                       (tree-node (tree-head tree)
                                  (tree-left tree)
                                  left$)
                       right$))))))
