; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../notation/semantics")

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ subtree-operations
  :parents (tree-operations)
  :short "Some operations related to subtrees of ABNF trees."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines trees-in-trees
  :short "Set of all the trees
          in trees, lists of trees, and lists of lists of trees."

  (define trees-in-tree ((tree treep))
    :returns (treeset tree-setp)
    :parents (semantics trees-in-trees)
    :short "Set of all the trees in a tree."
    :long
    (xdoc::topstring
     (xdoc::p
      "This includes the tree itself,
       as well as all the trees recursively found in the branches."))
    (tree-case
     tree
     :leafterm (set::insert (tree-fix tree) nil)
     :leafrule (set::insert (tree-fix tree) nil)
     :nonleaf (set::insert (tree-fix tree)
                           (trees-in-tree-list-list tree.branches)))
    :measure (tree-count tree)

    ///

    (defret tree-member-of-trees-in-tree
      (set::in (tree-fix tree) treeset)
      :hints (("Goal" :expand ((trees-in-tree tree))))))

  (define trees-in-tree-list ((trees tree-listp))
    :returns (treeset tree-setp)
    :parents (semantics trees-in-trees)
    :short "Set of all the trees in a list of trees."
    :long
    (xdoc::topstring
     (xdoc::p
      "We take the union of the trees in all the trees of the list."))
    (cond ((endp trees) nil)
          (t (set::union (trees-in-tree (car trees))
                         (trees-in-tree-list (cdr trees)))))
    :measure (tree-list-count trees))

  (define trees-in-tree-list-list ((treess tree-list-listp))
    :returns (treeset tree-setp)
    :parents (semantics trees-in-trees)
    :short "Set of all the trees in a list of lists of trees."
    :long
    (xdoc::topstring
     (xdoc::p
      "We take the union of the trees in all the lists of trees of the list."))
    (cond ((endp treess) nil)
          (t (set::union (trees-in-tree-list (car treess))
                         (trees-in-tree-list-list (cdr treess)))))
    :measure (tree-list-list-count treess))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual trees-in-trees))
