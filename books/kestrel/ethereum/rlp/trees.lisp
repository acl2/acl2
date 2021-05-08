; Ethereum Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "../basics")

(local (include-book "kestrel/utilities/lists/len-const-theorems" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes rlp-trees
  :parents nil

  (fty::deftagsum rlp-tree
    :parents (rlp)
    :short "RLP trees."
    :long
    (xdoc::topstring
     (xdoc::p
      "An RLP tree has
       a <see topic='@(url byte-arrays)'>byte array</see> at each leaf.
       A branching node of the tree carries no additional information
       besides the structure implied by
       the sequence of its (zero or more) subtrees.")
     (xdoc::p
      "The definition of type @('rlp-tree')
       corresponds to @($\\mathbb{T}$) [YP:(176)].
       The definition of type @('rlp-tree-list')
       corresponds to @($\\mathbb{L}$) [YP:(177)];
       we use true lists to model sequences of subtrees.")
     (xdoc::p
      "These trees are called `items' in [Wiki:RLP];
       we prefer the term `tree', because it seems clearer.
       The byte sequences at the leaves are called
       `byte arrays' in [YP:B] and [Wiki:RLP], and also `strings' in [Wiki:RLP];
       we prefer the former term, because it seems clearer."))
    (:leaf ((bytes byte-list)))
    (:branch ((subtrees rlp-tree-list)))
    :pred rlp-treep

    ///

    (defrule rlp-tree-leaf->bytes-injective
      (implies (and (rlp-tree-case x :leaf)
                    (rlp-tree-case y :leaf))
               (equal (equal (rlp-tree-leaf->bytes x)
                             (rlp-tree-leaf->bytes y))
                      (equal (rlp-tree-fix x)
                             (rlp-tree-fix y))))
      :enable (rlp-treep
               rlp-tree-kind
               rlp-tree-leaf->bytes
               rlp-tree-fix
               acl2::equal-len-const))

    (defrule rlp-tree-branch->subtrees-injective
      (implies (and (rlp-tree-case x :branch)
                    (rlp-tree-case y :branch))
               (equal (equal (rlp-tree-branch->subtrees x)
                             (rlp-tree-branch->subtrees y))
                      (equal (rlp-tree-fix x)
                             (rlp-tree-fix y))))
      :enable (rlp-tree-branch->subtrees
               rlp-tree-fix)))

  (fty::deflist rlp-tree-list
    :parents (rlp-tree)
    :short "True lists of RLP trees."
    :elt-type rlp-tree
    :true-listp t
    :elementp-of-nil nil
    :pred rlp-tree-listp))
