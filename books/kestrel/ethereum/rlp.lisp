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
(include-book "kestrel/utilities/digits-any-base/core" :dir :system)

(local (include-book "std/lists/top" :dir :system))

(include-book "basics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rlp
  :parents (ethereum)
  :short "Recursive Length Prefix (RLP)."
  :long
  (xdoc::topp
   "RLP is a serialization (encoding) method for Ethereum,
    described in [YP:B] and in
    <a href=\"https://github.com/ethereum/wiki/wiki/RLP\">Page `RLP'
    of [Wiki]</a>;
    we reference that page of [Wiki] as `[Wiki:RLP]').")
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection rlp-big-endian-representations
  :parents (rlp)
  :short "Big-endian representation of scalars in RLP."
  :long
  (xdoc::topapp
   (xdoc::p
    "The library function @(tsee nat=>bendian*),
     when the @('base') argument is 256,
     corresponds to @($\\mathtt{BE}$) [YP:(181)].
     Note that no leading 0 is allowed, even for representing 0,
     which is thus represented by the empty list of digits.")
   (xdoc::p
    "Digits in base 256 are bytes.
     We introduce return type theorems for @(tsee nat=>bendian*)
     (and for the other number-to-digit conversions,
     even though we do not use them here)."))

  (defruled dab-digit-listp-of-256-is-byte-listp
    (equal (acl2::dab-digit-listp 256 digits)
           (byte-listp digits))
    :enable (acl2::dab-digit-listp acl2::dab-digitp byte-listp bytep))

  (acl2::defthm-dab-return-types
   dab-digit-listp-of-256-is-byte-listp
   byte-listp-of))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-encode-bytes ((bytes byte-listp))
  :parents (rlp)
  :returns (mv (error? booleanp)
               (encoding byte-listp
                         :hints (("Goal"
                                  :in-theory (enable bytep)
                                  :use (:instance
                                        acl2::len-of-nat=>bendian*-leq-width
                                        (nat (len bytes))
                                        (base 256)
                                        (width 8))))))
  :short "RLP encoding of a byte array."
  :long
  (xdoc::topapp
   (xdoc::p
    "This corresponds to @($R_{\\mathrm{b}}$) [YP:(180)].")
   (xdoc::p
    "That equation does not explicitly say that the byte array
     can be encoded only if its length is below @($2^{64}$).
     This can be inferred from the fact that, according to [YP:(183)],
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
     The encoding code in [Wiki:RLP] confirms this, via an explicit check.")
   (xdoc::p
    "The first result of this function is an error flag,
     which is @('t') if the argument byte array cannot be encoded;
     in this case, @('nil') is returned as the (irrelevant) second result."))
  (b* ((bytes (byte-list-fix bytes)))
    (cond ((and (= (len bytes) 1)
                (< (car bytes) 128)) (mv nil bytes))
          ((< (len bytes) 56) (b* ((encoding (cons (+ 128 (len bytes))
                                                   bytes)))
                                (mv nil encoding)))
          ((< (len bytes)
              (expt 2 64)) (b* ((be (nat=>bendian* 256 (len bytes)))
                                (encoding (cons (+ 183 (len be))
                                                (append be bytes))))
                             (mv nil encoding)))
          (t (mv t nil))))
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines rlp-encode-tree
  :parents (rlp)
  :short "RLP encoding of a tree."
  :long
  (xdoc::topapp
   (xdoc::p
    "This corresponds to
     @($\\mathtt{RLP}$) [YP:(179)],
     @($R_{\\mathrm{l}}$) [YP:(183)],
     and @($s$) [YP:(184)].
     More precisely,
     @(tsee rlp-encode-tree) corresponds to @($\\mathtt{RLP}$),
     the non-leaf case of @(tsee rlp-encode-tree)
     corresponds to @($R_{\\mathrm{l}}$),
     and @(tsee rlp-encode-tree-list) corresponds to @($s$).")
   (xdoc::p
    "[YP:(183)] does not explicitly say that the tree can be encoded
     only if the total length of its encoded subtrees is below @($2^{64}$).
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
     The encoding code in [Wiki:RLP] confirms this, via an explicit check.")
   (xdoc::p
    "Similarly, [YP:(184)] does not explicitly say that
     the concatenation of the encoded subtrees
     cannot be encoded if any subtree cannot be encoded.
     This can be inferred from the fact that if a subtree encoding is too long,
     the supertree encoding is at least that long.
     The encoding code in [Wiki:RLP] confirms this, by propagating exceptions.")
   (xdoc::p
    "The first result of this function is an error flag,
     which is @('t') if the argument tree cannot be encoded;
     in this case, @('nil') is returned as the (irrelevant) second result.")
   (xdoc::def "rlp-encode-tree")
   (xdoc::def "rlp-encode-tree-list"))
  :verify-guards nil ; done below

  (define rlp-encode-tree ((tree rlp-treep))
    :returns (mv (error? booleanp)
                 (encoding byte-listp))
    (rlp-tree-case
     tree
     :leaf (rlp-encode-bytes tree.bytes)
     :nonleaf (b* (((mv error? encoding) (rlp-encode-tree-list tree.subtrees))
                   ((when error?) (mv t nil)))
                (cond ((< (len encoding) 56)
                       (b* ((encoding (cons (+ 192 (len encoding))
                                            encoding)))
                         (mv nil encoding)))
                      ((< (len encoding)
                          (expt 2 64))
                       (b* ((be (nat=>bendian* 256 (len encoding)))
                            (encoding (cons (+ 247 (len be))
                                            (append be encoding))))
                         (mv nil encoding)))
                      (t (mv t nil)))))
    :measure (rlp-tree-count tree)
    :no-function t)

  (define rlp-encode-tree-list ((trees rlp-tree-listp))
    :returns (mv (error? booleanp)
                 (encoding byte-listp))
    (b* (((when (endp trees)) (mv nil nil))
         ((mv error? encoding1) (rlp-encode-tree (car trees)))
         ((when error?) (mv t nil))
         ((mv error? encoding2) (rlp-encode-tree-list (cdr trees)))
         ((when error?) (mv t nil)))
      (mv nil (append encoding1 encoding2)))
    :measure (rlp-tree-list-count trees)
    :no-function t)

  :returns-hints (("Goal"
                   :in-theory (enable bytep))
                  '(:use (:instance
                          acl2::len-of-nat=>bendian*-leq-width
                          (nat (len
                                (mv-nth 1 (rlp-encode-tree-list
                                           (rlp-tree-nonleaf->subtrees tree)))))
                          (base 256)
                          (width 8))))

  ///

  (verify-guards rlp-encode-tree
    :hints (("Goal"
             :in-theory (enable true-listp-when-byte-listp-rewrite))))

  (fty::deffixequiv-mutual rlp-encode-tree))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-encode-scalar ((nat natp))
  :returns (mv (error? booleanp)
               (encoding byte-listp))
  :parents (rlp)
  :short "RLP encoding of a scalar."
  :long
  (xdoc::topapp
   (xdoc::p
    "This corresponds to @($\\mathtt{RLP}$) [YP:(185)].")
   (xdoc::p
    "The first result of this function is an error flag,
     which is @('t') if the argument scalar is so large that
     its big-endian representation exceeds @($2^{64}$) in length."))
  (rlp-encode-bytes (nat=>bendian* 256 (lnfix nat)))
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk rlp-tree-encoding-p ((encoding byte-listp))
  :returns (yes/no booleanp)
  :parents (rlp)
  :short "Check if a byte array is an RLP encoding of a tree."
  :long
  (xdoc::topp
   "This is a declarative, non-executable definition,
    which essentially characterizes the image of @(tsee rlp-encode-tree)
    (over trees that can be encoded,
    i.e. such that @(tsee rlp-encode-tree) returns a @('nil') error flag).")
  (exists (tree)
          (and (rlp-treep tree)
               (b* (((mv tree-error? tree-encoding) (rlp-encode-tree tree)))
                 (and (not tree-error?)
                      (equal tree-encoding (byte-list-fix encoding))))))
  :skolem-name rlp-tree-encoding-witness
  ///

  (fty::deffixequiv rlp-tree-encoding-p
    :args ((encoding byte-listp))
    :hints (("Goal"
             :in-theory (disable rlp-tree-encoding-p-suff)
             :use ((:instance rlp-tree-encoding-p-suff
                    (tree (rlp-tree-encoding-witness (byte-list-fix encoding))))
                   (:instance rlp-tree-encoding-p-suff
                    (tree (rlp-tree-encoding-witness encoding))
                    (encoding (byte-list-fix encoding))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-decode-tree ((encoding byte-listp))
  :returns
  (mv (error? booleanp)
      (tree rlp-treep
            :hints (("Goal"
                     :in-theory
                     (e/d
                      (rlp-tree-encoding-p)
                      (rlp-tree-encoding-p-of-byte-list-fix-encoding))))))
  :parents (rlp)
  :short "RLP decoding of a tree."
  :long
  (xdoc::topapp
   (xdoc::p
    "If the byte array encodes some tree, we return that tree,
     along with a @('nil') error flag.
     Otherwise, we return a @('t') error flag,
     and an irrelevant tree as second result.")
   (xdoc::p
    "This is a declarative, non-executable definition,
     which says that decoding is the inverse of encoding.
     This is the intention of [YP:B], which only specifies encoding,
     leaving decoding implicit.")
   (xdoc::p
    "More precisely, we define decoding as the right inverse of encoding
     (with respect to byte arrays that are valid encodings of trees),
     as explicated by the theorem @('rlp-encode-tree-of-rlp-decode-tree').
     To prove that decoding is left inverse of encoding
     (with respect to trees that can be encoded),
     we need to show that encoding is injective over trees that can be encoded.
     We conjecture that the proof of this property
     may be a by-product of deriving an executable implementation of decoding
     via stepwise refinement
     (e.g. using <see topic='@(url apt::apt)'>APT</see>):
     if there were two different trees whose encodings are equal,
     an executable implementation of decoding, which returns a unique tree,
     could not be shown to be equal to @('rlp-tree-endoding-witness'),
     which is introduced by a @(tsee defchoose) inside @(tsee defun-sk)
     and therefore could be either tree.
     Thus, we defer the injectivity and left inverse proofs for now.")
   (xdoc::p
    "The decoding code in [Wiki:RLP] provides a reference implementation.
     Note that it is considerably more complicated than the encoding code.
     Thus, our high-level specification of decoding seems appropriate."))
  (b* ((encoding (byte-list-fix encoding)))
    (if (rlp-tree-encoding-p encoding)
        (mv nil (rlp-tree-encoding-witness encoding))
      (mv t (rlp-tree-leaf nil))))
  :no-function t
  :hooks (:fix)
  ///

  (defrule rlp-encode-tree-of-rlp-decode-tree
    (implies (and (byte-listp encoding)
                  (rlp-tree-encoding-p encoding))
             (b* (((mv d-error? d-tree) (rlp-decode-tree encoding))
                  ((mv e-error? e-encoding) (rlp-encode-tree d-tree)))
               (and (not d-error?)
                    (not e-error?)
                    (equal e-encoding encoding))))
    :enable rlp-tree-encoding-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk rlp-bytes-encoding-p ((encoding byte-listp))
  :returns (yes/no booleanp)
  :parents (rlp)
  :short "Check if a byte array is an RLP encoding of a byte array."
  :long
  (xdoc::topapp
   (xdoc::p
    "This is analogous to @(tsee rlp-tree-encoding-p).")
   (xdoc::p
    "The encoding of a byte array
     is also the encoding of a tree consisting of a single leaf
     with that byte array."))
  (exists (bytes)
          (and (byte-listp bytes)
               (b* (((mv bytes-error? bytes-encoding) (rlp-encode-bytes bytes)))
                 (and (not bytes-error?)
                      (equal bytes-encoding (byte-list-fix encoding))))))
  :skolem-name rlp-bytes-encoding-witness
  ///

  (fty::deffixequiv rlp-bytes-encoding-p
    :args ((encoding byte-listp))
    :hints (("Goal"
             :in-theory (disable rlp-bytes-encoding-p-suff)
             :use ((:instance rlp-bytes-encoding-p-suff
                    (bytes (rlp-bytes-encoding-witness (byte-list-fix encoding))))
                   (:instance rlp-bytes-encoding-p-suff
                    (bytes (rlp-bytes-encoding-witness encoding))
                    (encoding (byte-list-fix encoding)))))))

  (defruled rlp-tree-encoding-p-when-rlp-bytes-encoding-p
    (implies (rlp-bytes-encoding-p encoding)
             (rlp-tree-encoding-p encoding))
    :use (:instance rlp-tree-encoding-p-suff
          (tree (rlp-tree-leaf (rlp-bytes-encoding-witness encoding))))
    :enable rlp-encode-tree))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-decode-bytes ((encoding byte-listp))
  :returns
  (mv (error? booleanp)
      (bytes byte-listp
             :hints (("Goal"
                      :in-theory
                      (e/d (rlp-bytes-encoding-p)
                           (rlp-bytes-encoding-p-of-byte-list-fix-encoding))))))
  :parents (rlp)
  :short "RLP decoding of a byte array."
  :long
  (xdoc::topapp
   (xdoc::p
    "This is analogous to @(tsee rlp-decode-tree).
     An analogous remark about left inverse and injectivity applies here.
     If the returned error flag is @('t'),
     we return @('nil') as the (irrelevant) second result.")
   (xdoc::p
    "The encoding of a leaf tree via @(tsee rlp-encode-tree) is the same as
     the encoding of the byte array at the leaf via @(tsee rlp-encode-bytes).
     To show the corresponding relationship about the decoding functions,
     we need the injectivity of encoding;
     otherwise, the two witness functions could yield ``incompatible'' values.
     Thus, we defer the proof of this relationship for now."))
  (b* ((encoding (byte-list-fix encoding)))
    (if (rlp-bytes-encoding-p encoding)
        (mv nil (rlp-bytes-encoding-witness encoding))
      (mv t nil)))
  :no-function t
  :hooks (:fix)
  ///

  (defrule rlp-encode-bytes-of-rlp-decode-bytes
    (implies (and (byte-listp encoding)
                  (rlp-bytes-encoding-p encoding))
             (b* (((mv d-error? d-bytes) (rlp-decode-bytes encoding))
                  ((mv e-error? e-encoding) (rlp-encode-bytes d-bytes)))
               (and (not d-error?)
                    (not e-error?)
                    (equal e-encoding encoding))))
    :enable rlp-bytes-encoding-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk rlp-scalar-encoding-p ((encoding byte-listp))
  :returns (yes/no booleanp)
  :parents (rlp)
  :short "Check if a byte array is an RLP encoding of a scalar."
  :long
  (xdoc::topp
   "This is analogous to @(tsee rlp-tree-encoding-p).")
  (exists (nat)
          (and (natp nat)
               (b* (((mv nat-error? nat-bytes) (rlp-encode-scalar nat)))
                 (and (not nat-error?)
                      (equal nat-bytes (byte-list-fix encoding))))))
  :skolem-name rlp-scalar-encoding-witness
  ///

  (fty::deffixequiv rlp-scalar-encoding-p
    :args ((encoding byte-listp))
    :hints (("Goal"
             :in-theory (disable rlp-scalar-encoding-p-suff)
             :use ((:instance rlp-scalar-encoding-p-suff
                    (nat (rlp-scalar-encoding-witness
                          (byte-list-fix encoding))))
                   (:instance rlp-scalar-encoding-p-suff
                    (nat (rlp-scalar-encoding-witness encoding))
                    (encoding (byte-list-fix encoding))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-decode-scalar ((encoding byte-listp))
  :returns
  (mv (error? booleanp)
      (scalar natp
              :hints (("Goal"
                       :in-theory
                       (e/d
                        (rlp-scalar-encoding-p)
                        (rlp-scalar-encoding-p-of-byte-list-fix-encoding))))))
  :parents (rlp)
  :short "RLP decoding of a scalar."
  :long
  (xdoc::topapp
   (xdoc::p
    "This is analogous to @(tsee rlp-decode-tree).
     An analogous remark about left inverse and injectivity applies here.
     If the returned error flag is @('t'),
     we return 0 as the (irrelevant) second result.")
   (xdoc::p
    "The encoding of a scalar via @(tsee rlp-encode-scalar) is the same as
     the encoding of the big-endian byte array via @(tsee rlp-encode-bytes).
     To show the corresponding relationship about the decoding functions,
     we need the injectivity of encoding;
     otherwise, the two witness functions could yield ``incompatible'' values.
     Thus, we defer the proof of this relationship for now."))
  (b* ((encoding (byte-list-fix encoding)))
    (if (rlp-scalar-encoding-p encoding)
        (mv nil (rlp-scalar-encoding-witness encoding))
      (mv t 0)))
  :no-function t
  :hooks (:fix)
  ///

  (defrule rlp-encode-scalar-of-rlp-decode-scalar
    (implies (and (byte-listp encoding)
                  (rlp-scalar-encoding-p encoding))
             (b* (((mv d-error? d-scalar) (rlp-decode-scalar encoding))
                  ((mv e-error? e-encoding) (rlp-encode-scalar d-scalar)))
               (and (not d-error?)
                    (not e-error?)
                    (equal e-encoding encoding))))
    :enable rlp-scalar-encoding-p))
