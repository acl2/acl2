; Ethereum Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "decodability")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rlp-decoding-declarative
  :parents (rlp)
  :short "Declarative definitions of RLP decoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "We specify RLP decoding via functions
     from byte arrays
     to byte arrays, trees, and scalars.
     These functions are declaratively defined
     as inverses of the RLP encoding functions.
     They are not executable.")
   (xdoc::p
    "Note that [YP:B] only defines RLP encoding explicitly, not RLP decoding.
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
  (xdoc::topstring
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
     as explicated by the theorem @('rlp-encode-tree-of-rlp-decode-tree').")
   (xdoc::p
    "We use the injectivity of @(tsee rlp-encode-tree),
     proved <see topic='@(url rlp-decodability)'>here</see>,
     to prove that decoding is also the left inverse of encoding
     (with respect to encodable trees),
     as the theorem @('rlp-decode-tree-of-rlp-encode-tree').
     Roughly speaking, the proof goes like this:
     (1) instantiate the right identity theorem,
     namely @('(encode (decode y)) = y'),
     with @('y') replaced with @('(encode x)'),
     obtaining @('(encode (decode (encode x))) = (encode x)');
     (2) use the injectivity of @('encode')
     to obtain @('(decode (encode x)) = x').
     Note that we disable both the right inverse theorem
     and the definition of @(tsee rlp-decode-tree),
     which would otherwise sabotage this proof.")
   (xdoc::p
    "The decoding code in [Wiki:RLP] provides a reference implementation.
     Note that it is considerably more complicated than the encoding code.
     Our high-level specification of decoding is simpler."))
  (b* ((encoding (byte-list-fix encoding)))
    (if (rlp-tree-encoding-p encoding)
        (mv nil (rlp-tree-encoding-witness encoding))
      (mv t (rlp-tree-leaf nil))))
  :no-function t
  :hooks (:fix)
  ///

  (defrule rlp-encode-tree-of-rlp-decode-tree
    (implies (rlp-tree-encoding-p encoding)
             (b* (((mv d-error? tree) (rlp-decode-tree encoding))
                  ((mv e-error? encoding1) (rlp-encode-tree tree)))
               (and (not d-error?)
                    (not e-error?)
                    (equal encoding1
                           (byte-list-fix encoding))))))

  (defrule rlp-decode-tree-of-rlp-encode-tree
    (b* (((mv e-error? encoding) (rlp-encode-tree tree))
         ((mv d-error? tree1) (rlp-decode-tree encoding)))
      (implies (not e-error?)
               (and (not d-error?)
                    (equal tree1
                           (rlp-tree-fix tree)))))
    :use (:instance rlp-encode-tree-of-rlp-decode-tree
          (encoding (mv-nth 1 (rlp-encode-tree tree))))
    :disable (rlp-decode-tree
              rlp-encode-tree-of-rlp-decode-tree)))

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
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee rlp-decode-tree).
     If the returned error flag is @('t'),
     we return @('nil') as the (irrelevant) second result.")
   (xdoc::p
    "As proved in @(tsee rlp-bytes-encoding-p),
     the encoding of a byte array
     is also the encoding of the leaf tree containing the byte array.
     Because @(tsee rlp-encode-tree) is injective,
     the two witnesses (decoders)
     @('rlp-bytes-encoding-witness') and @('rlp-tree-encoding-witness')
     are related accordingly.
     Roughly speaking, the proof goes like this:
     (1) start with the fact that @('rlp-bytes-encoding-witness')
     is right inverse of @(tsee rlp-encode-bytes),
     i.e. @('rlp-encode-bytes o rlp-bytes-encoding-witness = id'),
     where @('o') is function composition and @('id') is the identity function;
     (2) use the alternative definition of @(tsee rlp-encode-bytes)
     in terms of @(tsee rlp-encode-tree) to obtain
     @('rlp-encode-tree o rlp-tree-leaf o rlp-bytes-encoding-witness = id');
     (3) use the fact that @('rlp-tree-encoding-witness')
     is right inverse of @(tsee rlp-encode-tree),
     i.e. @('rlp-encode-tree o rlp-tree-encoding-witness = id');
     (4) from (2) and (3) and the injectivity of @(tsee rlp-encode-tree), derive
     @('rlp-tree-encoding-witness =
        rlp-tree-leaf o rlp-bytes-encoding-witness').
     It is generally the case that
     if an injective function has two right inverses, they are equal.")
   (xdoc::p
    "This relationship among these witnesses lets us prove a theorem
     that provides an alternative definition of @(tsee rlp-decode-bytes)
     in terms of @(tsee rlp-decode-tree)."))
  (b* ((encoding (byte-list-fix encoding)))
    (if (rlp-bytes-encoding-p encoding)
        (mv nil (rlp-bytes-encoding-witness encoding))
      (mv t nil)))
  :no-function t
  :hooks (:fix)
  ///

  (defrule rlp-encode-bytes-of-rlp-decode-bytes
    (implies (rlp-bytes-encoding-p encoding)
             (b* (((mv d-error? bytes) (rlp-decode-bytes encoding))
                  ((mv e-error? encoding1) (rlp-encode-bytes bytes)))
               (and (not d-error?)
                    (not e-error?)
                    (equal encoding1
                           (byte-list-fix encoding))))))

  (defrule rlp-decode-bytes-of-rlp-encode-bytes
    (b* (((mv e-error? encoding) (rlp-encode-bytes bytes))
         ((mv d-error? bytes1) (rlp-decode-bytes encoding)))
      (implies (not e-error?)
               (and (not d-error?)
                    (equal bytes1
                           (byte-list-fix bytes)))))
    :use (:instance rlp-encode-bytes-of-rlp-decode-bytes
          (encoding (mv-nth 1 (rlp-encode-bytes bytes))))
    :disable (rlp-decode-bytes
              rlp-encode-bytes-of-rlp-decode-bytes))

  (defruled rlp-tree-encoding-witness-as-rlp-bytes-encoding-witness
    (implies (rlp-bytes-encoding-p encoding)
             (equal (rlp-tree-encoding-witness encoding)
                    (rlp-tree-leaf (rlp-bytes-encoding-witness encoding))))
    :use (rlp-encode-bytes-of-rlp-bytes-encoding-witness
          rlp-encode-tree-of-rlp-tree-encoding-witness)
    :disable (rlp-encode-bytes-of-rlp-bytes-encoding-witness
              rlp-encode-tree-of-rlp-tree-encoding-witness)
    :enable rlp-encode-bytes-alt-def)

  (defruled rlp-bytes-encoding-witness-as-rlp-tree-encoding-witness
    (implies (rlp-bytes-encoding-p encoding)
             (equal (rlp-bytes-encoding-witness encoding)
                    (rlp-tree-leaf->bytes (rlp-tree-encoding-witness encoding))))
    :use (rlp-encode-bytes-of-rlp-bytes-encoding-witness
          rlp-encode-tree-of-rlp-tree-encoding-witness)
    :disable (rlp-encode-bytes-of-rlp-bytes-encoding-witness
              rlp-encode-tree-of-rlp-tree-encoding-witness)
    :enable rlp-encode-bytes-alt-def)

  (theory-invariant
   (incompatible
    (:rewrite rlp-tree-encoding-witness-as-rlp-bytes-encoding-witness)
    (:rewrite rlp-bytes-encoding-witness-as-rlp-tree-encoding-witness)))

  (defruled rlp-decode-bytes-alt-def
    (equal (rlp-decode-bytes encoding)
           (b* (((mv error? tree) (rlp-decode-tree encoding))
                ((when error?) (mv t nil))
                ((unless (rlp-tree-case tree :leaf)) (mv t nil))
                (bytes (rlp-tree-leaf->bytes tree)))
             (mv nil bytes)))
    :enable (rlp-decode-tree
             rlp-tree-encoding-witness-as-rlp-bytes-encoding-witness)
    :use ((:instance rlp-bytes-encoding-p-when-rlp-tree-encoding-p-and-leaf
           (encoding (byte-list-fix encoding))))))

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
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee rlp-decode-tree).
     If the returned error flag is @('t'),
     we return 0 as the (irrelevant) second result.")
   (xdoc::p
    "Analogously to @(tsee rlp-decode-bytes),
     we use the injectivity of @(tsee rlp-encode-bytes)
     to prove a relationship between
     @('rlp-scalar-encoding-witness') and @('rlp-bytes-encoding-witness'),
     as well as a theorem that provides
     an alternative definition of @(tsee rlp-decode-scalar)
     in terms of @(tsee rlp-decode-bytes)."))
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
                           (byte-list-fix encoding))))))

  (defrule rlp-decode-scalar-of-rlp-encode-scalar
    (b* (((mv e-error? encoding) (rlp-encode-scalar scalar))
         ((mv d-error? scalar1) (rlp-decode-scalar encoding)))
      (implies (not e-error?)
               (and (not d-error?)
                    (equal scalar1
                           (nfix scalar)))))
    :use (:instance rlp-encode-scalar-of-rlp-decode-scalar
          (encoding (mv-nth 1 (rlp-encode-scalar scalar))))
    :disable (rlp-decode-scalar
              (:e rlp-decode-scalar) ; otherwise HIDE appears in the proof
              rlp-encode-scalar-of-rlp-decode-scalar))

  (defruled rlp-bytes-encoding-witness-as-rlp-scalar-encoding-witness
    (implies (rlp-scalar-encoding-p encoding)
             (equal (rlp-bytes-encoding-witness encoding)
                    (nat=>bebytes* (rlp-scalar-encoding-witness encoding))))
    :use (rlp-encode-scalar-of-rlp-scalar-encoding-witness
          rlp-encode-bytes-of-rlp-bytes-encoding-witness)
    :disable (rlp-encode-scalar-of-rlp-scalar-encoding-witness
              rlp-encode-bytes-of-rlp-bytes-encoding-witness)
    :enable (rlp-encode-scalar
             rlp-bytes-encoding-p-when-rlp-scalar-encoding-p))

  (defruled rlp-scalar-encoding-witness-as-rlp-bytes-encoding-witness
    (implies (rlp-scalar-encoding-p encoding)
             (equal (rlp-scalar-encoding-witness encoding)
                    (bebytes=>nat (rlp-bytes-encoding-witness encoding))))
    :use (rlp-bytes-encoding-witness-as-rlp-scalar-encoding-witness
          (:instance lemma
           (x (rlp-bytes-encoding-witness encoding))
           (y (nat=>bebytes* (rlp-scalar-encoding-witness encoding)))))

    :prep-lemmas
    ((defruled lemma
       (implies (equal x y)
                (equal (bebytes=>nat x)
                       (bebytes=>nat y))))))

  (theory-invariant
   (incompatible
    (:rewrite rlp-bytes-encoding-witness-as-rlp-scalar-encoding-witness)
    (:rewrite rlp-scalar-encoding-witness-as-rlp-bytes-encoding-witness)))

  (defruled rlp-decode-scalar-alt-def
    (equal (rlp-decode-scalar encoding)
           (b* (((mv error? bytes) (rlp-decode-bytes encoding))
                ((when error?) (mv t 0))
                ((unless (equal (trim-bendian* bytes) bytes)) (mv t 0))
                (scalar (bebytes=>nat bytes)))
             (mv nil scalar)))
    :enable (rlp-decode-bytes
             rlp-bytes-encoding-witness-as-rlp-scalar-encoding-witness)
    :use ((:instance natp-of-rlp-scalar-encoding-witness
           (encoding (byte-list-fix encoding)))
          (:instance
           rlp-scalar-encoding-p-when-rlp-bytes-encoding-p-and-no-leading-zeros
           (encoding (byte-list-fix encoding))))
    :disable natp-of-rlp-scalar-encoding-witness))
