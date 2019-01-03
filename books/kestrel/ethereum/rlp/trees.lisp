; Ethereum Library -- RLP Trees
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "../basics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes rlp-trees

  (fty::deftagsum rlp-tree
    :parents (rlp)
    :short "RLP trees."
    :long
    "<p>
     An RLP tree has
     a <see topic='@(url byte-arrays)'>byte array</see> at each leaf.
     A non-leaf node of the tree carries no additional information
     besides the structure implied by
     the sequence of its (zero or more) subtrees.
     </p>
     <p>
     The definition of type @('rlp-tree')
     corresponds to @($\\mathbb{T}$) [YP:(176)].
     The definition of type @('rlp-tree-list')
     corresponds to @($\\mathbb{L}$) [YP:(177)];
     we use true lists to model sequences of subtrees.
     </p>
     <p>
     These trees are called `items' in [Wiki:RLP];
     we prefer the term `tree', because it seems clearer.
     The byte sequences at the leaves are called
     `byte arrays' in [YP:B] and [Wiki:RLP], and also `strings' in [Wiki:RLP];
     we use the former term in preference to the latter,
     because it seems clearer.
     </p>
     <p>
     It may be unclear, at first,
     whether the empty sequence in @($\\mathbb{L}$) [YP:(177)]
     is distinct from
     the empty sequence in @($\\mathbb{B}$) [YP:(178)],
     and whether @($\\mathbb{T}$) [YP:(176)],
     which is defined as a non-disjoint union,
     contains a single empty sequence or two distinct ones.
     According to [YP:(180)] (see @(tsee rlp-encode-bytes)),
     the empty sequence from @($\\mathbb{B}$)
     is encoded as the singleton byte array containing 128.
     According to [YP:(183)] (see @(tsee rlp-encode-tree)),
     the empty sequence from @($\\mathbb{L}$)
     is encoded as the singleton byte array containing 192.
     Given these two different encodings, it seems reasonable to assume
     that the two empty sequences from the two sets are distinct.
     Accordingly, in our model of RLP trees,
     the leaf tree with the empty byte array is distinct from
     the non-leaf tree with no subtrees.
     This disambiguation is also supported by the fact that
     the code in [Wiki:RLP] treats those two empty sequences differently
     (one is a string, the other one is a list).
     </p>"
    (:leaf ((bytes byte-list)))
    (:nonleaf ((subtrees rlp-tree-list)))
    :pred rlp-treep)

  (fty::deflist rlp-tree-list
    :parents (rlp-tree)
    :short "True lists of RLP trees."
    :elt-type rlp-tree
    :true-listp t
    :pred rlp-tree-listp))
