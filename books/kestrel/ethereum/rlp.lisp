; Ethereum Library -- Recursive Length Prefix (RLP)
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/utilities/define-sk" :dir :system)
(include-book "kestrel/utilities/digits-any-base-pow2" :dir :system)

(local (include-book "std/lists/top" :dir :system))

(include-book "basics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc rlp
  :parents (ethereum)
  :short "Recursive Length Prefix (RLP)."
  :long
  "<p>
   RLP is a serialization (encoding) method for Ethereum,
   described in YP:B and in the `RLP' page of Wiki
   (which we refer to as `Wiki:RLP').
   </p>")

(xdoc::order-subtopics rlp nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc rlp-big-endian-representations
  :parents (rlp)
  :short "Big-endian representation of scalars in RLP."
  :long
  "<p>
   The library function @(tsee nat=>bendian*),
   when the @('base') argument is 256,
   corresponds to the function @($\\mathtt{BE}$), defined by YP:(181).
   Note that no leading 0 is allowed, even for representing 0,
   which is thus represented by the empty list of digits.
   </p>")

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
     corresponds to the set @($\\mathbb{T}$), defined by YP:(176).
     The definition of type @('rlp-tree-list')
     corresponds to the set @($\\mathbb{L}$), defined by YP:(177);
     we use true lists to model sequences of subtrees.
     </p>
     <p>
     These trees are called `items' in Wiki:RLP;
     we prefer the term `tree', because it seems clearer.
     The byte sequences at the leaves are called
     `byte arrays' in YP:B and Wiki:RLP, and also `strings' in Wiki:RLP;
     we use the former in preference to the latter,
     because it seems clearer.
     </p>
     <p>
     It may be unclear, at first,
     if the empty sequence in the set @($\\mathbb{L}$) in YP:(177)
     is distinct from
     the empty sequence in the set @($\\mathbb{B}$) in YP:(178),
     and if the set @($\\mathbb{T}$) in YP:(176),
     which is defined as a non-disjoint union,
     contains a single empty sequence or two distinct ones.
     According to YP:(180) (see @(tsee rlp-encode-bytes)),
     the empty sequence from the set @($\\mathbb{B}$)
     is encoded as the singleton byte array containing 128.
     According to YP:(183) (see @(tsee rlp-encode-tree)),
     the empty sequence from the set @($\\mathbb{L}$)
     is encoded as the singleton byte array containing 192.
     Given these two different encodings, it seems reasonable to assume
     that the two empty sequences from the two sets are distinct.
     Accordingly, in our model of RLP trees,
     the leaf tree with the empty byte array is distinct from
     the non-leaf tree with no subtrees.
     This disambiguation is also supported by the fact that
     the code in Wiki:RLP treats those two empty sequences differently
     (one is a string, the other one is a list).
     </p>"
    (:leaf ((bytes ubyte8-list)))
    (:nonleaf ((subtrees rlp-tree-list)))
    :pred rlp-treep)

  (fty::deflist rlp-tree-list
    :parents (rlp-tree)
    :short "True lists of RLP trees."
    :elt-type rlp-tree
    :true-listp t
    :pred rlp-tree-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflexsum rlp-tree/error
  :parents (rlp)
  :short "Union of @(':error') and RLP trees."
  :long
  "<p>
   These are the possible results of RLP decoding.
   </p>"
  (:error :fields () :ctor-body ':error :cond (eq x :error))
  (:bytes :fields ((tree :type rlp-tree :acc-body x)) :ctor-body tree)
  ///

  (defrule disjoint-tree/error
    (not (and (eq :error x)
              (rlp-treep x)))
    :rule-classes nil)

  (defrule rlp-tree/error-p-when-rlp-treep
    (implies (rlp-treep x)
             (rlp-tree/error-p x))
    :enable rlp-tree/error-p)

  (defrule rlp-tree/error-p-of-error
    (rlp-tree/error-p :error))

  (defrule rlp-treep-when-rlp-tree/error-p-and-not-error
    (implies (and (rlp-tree/error-p x)
                  (not (rlp-tree/error-case x :error)))
             (rlp-treep x))
    :enable rlp-tree/error-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-encode-bytes ((bytes ubyte8-listp))
  :parents (rlp)
  :returns (result ubyte8list/error-p
                   :hints (("Goal"
                            :in-theory (enable ubyte8p)
                            :use (:instance
                                  acl2::len-of-nat=>bendian*-leq-width
                                  (nat (len bytes))
                                  (base 256)
                                  (width 8)))))
  :short "RLP encoding of a byte array."
  :long
  "<p>
   This corresponds to the function @($R_{\\mathrm{b}}$), defined by YP:(180).
   </p>
   <p>
   That equation does not explicitly say that the byte array
   can be encoded only if its length is below @($2^{64}$).
   This can be inferred from the fact that, according to YP:(183),
   encodings whose first byte is 192 or higher
   are used for non-leaf trees.
   In order for the encoding to be unambiguous
   (in particular, to distinguish leaf trees from non-leaf trees),
   the first byte that encodes a byte array must be below 192.
   Thus, the length of the base-256 big-endian representation
   of the length of the byte array,
   which is added to 183, can be at most 8
   (reaching 191 for the first byte of the encoding).
   This means that the base-256 big-endian representation
   of the length of the byte array
   must have at most 8 digits,
   i.e. it must be below @($256^8$), which is @($2^{64}$).
   The encoding code in Wiki:RLP confirms this, via an explicit check.
   </p>
   <p>
   If a byte array cannot be encoded, we return @(':error').
   </p>"
  (b* ((bytes (ubyte8-list-fix bytes)))
    (cond ((and (= (len bytes) 1)
                (< (car bytes) 128)) bytes)
          ((< (len bytes) 56) (cons (+ 128 (len bytes))
                                    bytes))
          ((< (len bytes)
              (expt 2 64)) (b* ((be (nat=>bendian* 256 (len bytes))))
                             (cons (+ 183 (len be))
                                   (append be bytes))))
          (t :error)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines rlp-encode-tree
  :parents (rlp)
  :short "RLP encoding of a tree."
  :long
  "<p>
   This corresponds to
   the function @($\\mathtt{RLP}$) defined by YP:(179),
   the function @($R_{\\mathrm{l}}$) defined by YP:(183),
   and the function @($s$) defined by YP:(184).
   More precisely,
   @(tsee rlp-encode-tree) corresponds to @($\\mathtt{RLP}$),
   the non-leaf case of @(tsee rlp-encode-tree)
   corresponds to @($R_{\\mathrm{l}}$),
   and @(tsee rlp-encode-tree-list) corresponds to @($s$).
   </p>
   <p>
   YP:(183) does not explicitly say that the tree can be encoded
   only if the length of its encoded subtrees is below @($2^{64}$).
   This can be inferred from the fact that the first byte, being a byte,
   cannot exceed 255.
   Thus, the length of the base-256 big-endian representation
   of the length of the encoded subtrees,
   which is added to 247, can be at most 8
   (reaching 255 for the first byte of the encoding).
   This means that the base-256 big-endian representation
   of the length of the encoded subtrees
   must have at most 8 digits,
   i.e. it must be below @($256^8$), which is @($2^{64}$).
   The encoding code in Wiki:RLP confirms this, via an explicit check.
   </p>
   <p>
   Similarly, YP:(184) does not explicitly say that
   the concatenation of the encoded subtrees
   cannot be encoded if any subtree cannot be encoded.
   This can be inferred from the fact that if a subtree encoding is too long,
   the supertree encoding is also even longer.
   The encoding code in Wiki:RLP confirms this, by propagating exceptions.
   </p>
   <p>
   If a tree cannot be encoded, we return @(':error').
   </p>
   @(def rlp-encode-tree)
   @(def rlp-encode-tree-list)"
  :verify-guards nil ; done below

  (define rlp-encode-tree ((tree rlp-treep))
    :returns (result ubyte8list/error-p)
    (rlp-tree-case
     tree
     :leaf (rlp-encode-bytes tree.bytes)
     :nonleaf (b* ((bytes (rlp-encode-tree-list tree.subtrees))
                   ((when (ubyte8list/error-case bytes :error)) :error))
                (cond ((< (len bytes) 56) (cons (+ 192 (len bytes))
                                                bytes))
                      ((< (len bytes)
                          (expt 2 64)) (b* ((be (nat=>bendian* 256
                                                               (len bytes))))
                                         (cons (+ 247 (len be))
                                               (append be bytes))))
                      (t :error))))
    :measure (rlp-tree-count tree))

  (define rlp-encode-tree-list ((trees rlp-tree-listp))
    :returns (result ubyte8list/error-p)
    (b* (((when (endp trees)) nil)
         (bytes1 (rlp-encode-tree (car trees)))
         ((when (ubyte8list/error-case bytes1 :error)) :error)
         (bytes2 (rlp-encode-tree-list (cdr trees)))
         ((when (ubyte8list/error-case bytes2 :error)) :error))
      (append bytes1 bytes2))
    :measure (rlp-tree-list-count trees))

  :returns-hints (("Goal"
                   :in-theory (enable ubyte8p))
                  '(:use (:instance
                          acl2::len-of-nat=>bendian*-leq-width
                          (nat (len
                                (rlp-encode-tree-list
                                 (rlp-tree-nonleaf->subtrees tree))))
                          (base 256)
                          (width 8))))

  ///

  (verify-guards rlp-encode-tree
    :hints (("Goal"
             :in-theory (enable acl2::true-listp-when-ubyte8-listp-rewrite))))

  (fty::deffixequiv-mutual rlp-encode-tree))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-encode-scalar ((nat natp))
  :returns (result ubyte8list/error-p)
  :parents (rlp)
  :short "RLP encoding of a scalar."
  :long
  "<p>
   This corresponds to the function @($\\mathtt{RLP}$) defined by YP:(185).
   </p>
   <p>
   Note that @(':error') is returned if the scalar is so large that
   its big-endian representation exceeds @($2^{64}$) in length.
   </p>"
  (rlp-encode-bytes (nat=>bendian* 256 (lnfix nat)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk rlp-tree-encoding-p (x)
  :returns (yes/no booleanp)
  :parents (rlp)
  :short "Recognize RLP encodings of trees."
  :long
  "<p>
   This is a declarative, non-executable definition,
   which characterizes the image of @(tsee rlp-encode-tree)
   (over trees that can be encoded,
   i.e. such that @(tsee rlp-encode-tree) does not return @(':error')).
   </p>"
  (exists (tree)
          (and (rlp-treep tree)
               (equal (rlp-encode-tree tree)
                      x)
               (ubyte8-listp x)))
  :skolem-name rlp-tree-encoding-witness)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-decode-tree ((bytes ubyte8-listp))
  :returns (result rlp-tree/error-p
                   :hints (("Goal" :in-theory (enable rlp-tree-encoding-p))))
  :parents (rlp)
  :short "RLP decoding of a tree."
  :long
  "<p>
   If the byte array encodes some tree, we return that tree.
   Otherwise, we return @(':error').
   </p>
   <p>
   This is a declarative, non-executable definition,
   which says that decoding is the inverse of encoding.
   This is the intention of YP:B, which only specifies encoding,
   leaving decoding implicit.
   </p>
   <p>
   More precisely, we define decoding as the right inverse of encoding
   (over byte arrays that are valid encodings of trees),
   as explicated by the theorem @('rlp-encode-tree-of-rlp-decode-tree').
   To prove that decoding is left inverse of encoding
   (over trees that can be encoded),
   we need to show that encoding is injective over trees that can be encoded.
   We conjecture that the proof of this property
   may be a by-product of deriving an executable implementation of decoding
   via stepwise refinement (e.g. using <see topic='@(url apt::apt)'>APT</see>):
   if there were two different trees whose encodings are equal,
   an executable implementation of decoding, which returns a unique tree,
   could not be shown to be equal to @('rlp-tree-endoding-witness'),
   which is introduced by a @(tsee defchoose) inside @(tsee defun-sk)
   and therefore could be either tree.
   Thus, we defer the injectivity and left inverse proofs for now.
   </p>
   <p>
   The decoding code in Wiki:RLP provides a reference implementation.
   Note that it is considerably more complicated than the encoding code.
   Thus, our high-level specification of decoding seems appropriate.
   </p>"
  (b* ((bytes (ubyte8-list-fix bytes)))
    (if (rlp-tree-encoding-p bytes)
        (rlp-tree-encoding-witness bytes)
      :error))
  :hooks (:fix)
  ///

  (defrule rlp-encode-tree-of-rlp-decode-tree
    (implies (rlp-tree-encoding-p bytes)
             (equal (rlp-encode-tree (rlp-decode-tree bytes))
                    (ubyte8-list-fix bytes)))
    :enable rlp-tree-encoding-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk rlp-bytes-encoding-p (x)
  :returns (yes/no booleanp)
  :parents (rlp)
  :short "Recognize RLP encodings of byte arrays."
  :long
  "<p>
   This is analogous to @(tsee rlp-tree-encoding-p).
   </p>
   <p>
   The encoding of a byte array
   is also the encoding of a tree consisting of a single leaf
   with that byte array.
   </p>"
  (exists (bytes)
          (and (ubyte8-listp bytes)
               (equal (rlp-encode-bytes bytes)
                      x)
               (ubyte8-listp x)))
  :skolem-name rlp-bytes-encoding-witness
  ///

  (defruled rlp-tree-encoding-p-when-rlp-bytes-encoding-p
    (implies (rlp-bytes-encoding-p x)
             (rlp-tree-encoding-p x))
    :use (:instance rlp-tree-encoding-p-suff
          (tree (rlp-tree-leaf (rlp-bytes-encoding-witness x))))
    :enable rlp-encode-tree))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-decode-bytes ((bytes ubyte8-listp))
  :returns (result ubyte8list/error-p
                   :hints (("Goal" :in-theory (enable rlp-bytes-encoding-p))))
  :parents (rlp)
  :short "RLP decoding of a byte array."
  :long
  "<p>
   This is analogous to @(tsee rlp-decode-tree).
   An analogous remark about left inverse and injectivity applies here.
   </p>
   <p>
   The encoding of a leaf tree via @(tsee rlp-encode-tree) is the same as
   the encoding of the byte array at the leaf via @(tsee rlp-encode-bytes).
   To show the corresponding relationship about the decoding functions,
   we need the injectivity of encoding;
   otherwise, the two witness functions could yield ``incompatible'' values.
   Thus, we defer the proof of this relationship for now.
   </p>"
  (b* ((bytes (ubyte8-list-fix bytes)))
    (if (rlp-bytes-encoding-p bytes)
        (rlp-bytes-encoding-witness bytes)
      :error))
  :hooks (:fix)
  ///

  (defrule rlp-encode-bytes-of-rlp-decode-bytes
    (implies (rlp-bytes-encoding-p bytes)
             (equal (rlp-encode-bytes (rlp-decode-bytes bytes))
                    (ubyte8-list-fix bytes)))
    :enable rlp-bytes-encoding-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk rlp-scalar-encoding-p (x)
  :returns (yes/no booleanp)
  :parents (rlp)
  :short "Recognize RLP encodings of scalars."
  :long
  "<p>
   This is analogous to @(tsee rlp-tree-encoding-p).
   </p>"
  (exists (nat)
          (and (natp nat)
               (equal (rlp-encode-scalar nat)
                      x)
               (ubyte8-listp x)))
  :skolem-name rlp-scalar-encoding-witness)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-decode-scalar ((bytes ubyte8-listp))
  :returns (result nat/error-p
                   :hints (("Goal" :in-theory (enable rlp-scalar-encoding-p))))
  :parents (rlp)
  :short "RLP decoding of a scalar."
  :long
  "<p>
   This is analogous to @(tsee rlp-decode-tree).
   An analogous remark about left inverse and injectivity applies here.
   </p>
   <p>
   The encoding of a scalar via @(tsee rlp-encode-scalar) is the same as
   the encoding of the big-endian byte array via @(tsee rlp-encode-bytes).
   To show the corresponding relationship about the decoding functions,
   we need the injectivity of encoding;
   otherwise, the two witness functions could yield ``incompatible'' values.
   Thus, we defer the proof of this relationship for now.
   </p>"
  (b* ((bytes (ubyte8-list-fix bytes)))
    (if (rlp-scalar-encoding-p bytes)
        (rlp-scalar-encoding-witness bytes)
      :error))
  :hooks (:fix)
  ///

  (defrule rlp-encode-scalar-of-rlp-decode-scalar
    (implies (rlp-scalar-encoding-p bytes)
             (equal (rlp-encode-scalar (rlp-decode-scalar bytes))
                    (ubyte8-list-fix bytes)))
    :enable rlp-scalar-encoding-p))
