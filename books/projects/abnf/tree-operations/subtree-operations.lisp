; ABNF (Augmented Backus-Naur Form) Library
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
(local (include-book "std/basic/nfix" :dir :system))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod tree-path-step
  :short "Fixtype of steps of paths of subtrees in trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an element of a path of a subtree in a tree;
     see @(tsee tree-path).
     A non-leaf tree has a list of lists of trees as branches,
     corresponding to a concatenation of repetitions of elements.
     A step selects one of the trees in the branches:
     @('conc') selects a list of trees from the concatenation,
     corresponding to a repetition,
     and @('rep') selects a tree from the repetition,
     corresponding to an element."))
  ((conc nat)
   (rep nat))
  :pred tree-path-stepp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist tree-path
  :short "Fixtype of paths of subtrees in trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "A path is a list of zero or more steps (see @(tsee tree-path-step)),
     which navigate from the root of a tree towards the leaves of the tree.
     The empty path is the path of the whole tree,
     as a (non-strict) subtree of itself."))
  :elt-type tree-path-step
  :true-listp t
  :elementp-of-nil nil
  :pred tree-pathp)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist tree-path-list
  :short "Fixtype of lists of paths of subtrees in trees."
  :elt-type tree-path
  :true-listp t
  :elementp-of-nil t
  :pred tree-path-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defset tree-path-set
  :short "Fixtype of sets of paths of subtrees in trees."
  :elt-type tree-path
  :elementp-of-nil t
  :pred tree-path-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tree-path ((path tree-pathp) (tree treep))
  :returns (tree? tree-optionp)
  :short "Check if a path is valid in a tree,
          returning the subtree if successful."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if the paths stays within the tree,
     reaching a subtree of the treee,
     which we return.
     Otherwise we return @('nil').")
   (xdoc::p
    "The empty path is always valid.
     A non-empty path is valid iff
     the tree is a non-leaf tree,
     the first step of the path selects
     an existing subtree in the branches,
     and the rest of the path is valid for the subtree."))
  (b* (((when (endp path)) (tree-fix tree))
       ((unless (tree-case tree :nonleaf)) nil)
       ((tree-path-step step) (car path))
       (subtreess (tree-nonleaf->branches tree))
       ((unless (< step.conc (len subtreess))) nil)
       (subtrees (nth step.conc subtreess))
       ((unless (< step.rep (len subtrees))) nil)
       (subtree (nth step.rep subtrees)))
    (check-tree-path (cdr path) subtree))
  :guard-hints (("Goal" :in-theory (enable true-listp-when-tree-listp))))

;;;;;;;;;;;;;;;;;;;;

(define tree-at-path ((path tree-pathp) (tree abnf::treep))
  :guard (check-tree-path path tree)
  :returns (sub abnf::treep)
  :short "Subtree of a tree at a valid path."
  (tree-fix (check-tree-path path tree)))
