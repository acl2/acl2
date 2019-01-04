; Ethereum Library -- RLP Decoding Declarative Definitions
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "encoding")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rlp-decoding-declarative
  :parents (rlp)
  :short "Declarative definitions of RLP decoding."
  :long
  (xdoc::topapp
   (xdoc::p
    "We specify RLP decoding via functions
     from byte arrays
     to byte arrays, trees, and scalars.
     These functions are declaratively defined as inverses of
     the RLP encoding functions.
     They are not executable.")
   (xdoc::p
    "Note that [YP:B] only defines RLP encoding explicitly,
     but not RLP decoding.
     Clearly, the intention is that decoding is the inverse of encoding:
     this is the implicit specification of decoding in [YP:B]."))
  :order-subtopics t)

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
  :parents (rlp-decoding-declarative)
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
    (implies (rlp-tree-encoding-p encoding)
             (b* (((mv d-error? d-tree) (rlp-decode-tree encoding))
                  ((mv e-error? e-encoding) (rlp-encode-tree d-tree)))
               (and (not d-error?)
                    (not e-error?)
                    (equal e-encoding
                           (byte-list-fix encoding)))))
    :use (:instance lemma (encoding (byte-list-fix encoding)))

    :prep-lemmas
    ((defruled lemma
       (implies (and (byte-listp encoding)
                     (rlp-tree-encoding-p encoding))
                (b* (((mv d-error? d-tree) (rlp-decode-tree encoding))
                     ((mv e-error? e-encoding) (rlp-encode-tree d-tree)))
                  (and (not d-error?)
                       (not e-error?)
                       (equal e-encoding encoding))))
       :enable rlp-tree-encoding-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-decode-bytes ((encoding byte-listp))
  :returns
  (mv (error? booleanp)
      (bytes byte-listp
             :hints (("Goal"
                      :in-theory
                      (e/d (rlp-bytes-encoding-p)
                           (rlp-bytes-encoding-p-of-byte-list-fix-encoding))))))
  :parents (rlp-decoding-declarative)
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
    (implies (rlp-bytes-encoding-p encoding)
             (b* (((mv d-error? d-bytes) (rlp-decode-bytes encoding))
                  ((mv e-error? e-encoding) (rlp-encode-bytes d-bytes)))
               (and (not d-error?)
                    (not e-error?)
                    (equal e-encoding
                           (byte-list-fix encoding)))))
    :use (:instance lemma (encoding (byte-list-fix encoding)))

    :prep-lemmas
    ((defruled lemma
       (implies (and (byte-listp encoding)
                     (rlp-bytes-encoding-p encoding))
                (b* (((mv d-error? d-bytes) (rlp-decode-bytes encoding))
                     ((mv e-error? e-encoding) (rlp-encode-bytes d-bytes)))
                  (and (not d-error?)
                       (not e-error?)
                       (equal e-encoding encoding))))
       :enable rlp-bytes-encoding-p))))

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
  :parents (rlp-decoding-declarative)
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
    (implies (rlp-scalar-encoding-p encoding)
             (b* (((mv d-error? d-scalar) (rlp-decode-scalar encoding))
                  ((mv e-error? e-encoding) (rlp-encode-scalar d-scalar)))
               (and (not d-error?)
                    (not e-error?)
                    (equal e-encoding
                           (byte-list-fix encoding)))))
    :use (:instance lemma (encoding (byte-list-fix encoding)))

    :prep-lemmas
    ((defrule lemma
       (implies (and (byte-listp encoding)
                     (rlp-scalar-encoding-p encoding))
                (b* (((mv d-error? d-scalar) (rlp-decode-scalar encoding))
                     ((mv e-error? e-encoding) (rlp-encode-scalar d-scalar)))
                  (and (not d-error?)
                       (not e-error?)
                       (equal e-encoding encoding))))
       :enable rlp-scalar-encoding-p))))
