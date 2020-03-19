; Ethereum Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/crypto/ecdsa/secp256k1-interface" :dir :system)
(include-book "kestrel/crypto/interfaces/keccak-256" :dir :system)
(include-book "bytes")
(include-book "words")
(include-book "rlp/encoding")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transactions
  :parents (ethereum)
  :short "Transactions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Transactions are described in [YP:4.2].
     We define a high-level fixtype for transactions,
     and functions to RLP-encode/decode them."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-byte-list20
  byte-list20
  :parents (transactions)
  :short "Fixtype of byte arrays of length 20 and @('nil')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @($\\mathbf{to}$) field of a transaction [YP:4.2] is
     either a 20-byte (i.e. 160-bit) address
     or the empty array (i.e. the only element of @($\\mathbb{B}_0$)) [YP:(18)].
     Both [YP:4.2] and [YP:(18)] mention @($\\varnothing$) as
     the (only) element of @($\\mathbb{B}_0$);
     however, according to the definition of @($\\mathbb{B}$) [YP:(178)],
     the empty array should be denoted as @($()$).")
   (xdoc::p
    "Regardless, in our model the empty byte array is @('nil'),
     so we use either a list of 20 bytes or @('nil')
     to model the @($\\mathbf{to}$) field of a transaction."))
  :pred maybe-byte-list20p
  ///

  (defrule byte-listp-when-maybe-byte-list20p
    (implies (maybe-byte-list20p x)
             (byte-listp x))
    :enable maybe-byte-list20p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod transaction
  :parents (transactions)
  :short "Fixtype of transactions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A transaction is a 9-tuple [YP:(15)].
     The type of each component is specified in [YP:(16)].")
   (xdoc::p
    "We use @(see words) to model natural numbers in @($\\mathbb{N}_{256}$):
     this is the type of the nonce, gas price, gas limit, and value fields.")
   (xdoc::p
    "The type of the recipient field is @(tsee maybe-byte-list20).
     See the documentation of that fixtype for details.")
   (xdoc::p
    "The sixth component of the tuple is always a byte array,
     whether it is initialization code (when the recipient is @('nil'))
     or it is data (when the recipient is an address).")
   (xdoc::p
    "The remaining three components are for the signature.
     The @($\\mathbf{r}$) and @($\\mathbf{s}$) components are words.
     The other signature component is
     @($\\mathbf{v}$) in the text that describes it in [YP:4.2],
     but it is denoted as @($T_{\\mathrm{w}}$) in [YP:(15)] and [YP:(16)]
     (presumably to avoid a conflict with
     the @($T_{\\mathrm{v}}$) value component).
     We pick @('sign-v') (instead of @('sign-w'))
     for the corresponding field name in our product fixtype.
     However, there is an issue with the type of this component:
     [YP:(16)] says that it is a natural number below 32,
     but [YP:F] says that @($T_{\\mathrm{w}}$) may be
     a chain identifier doubled plus 35 or 36,
     in which case it is above 32.
     It looks like [YP:F] was updated according to [EIP155],
     while [YP:4.2] was not;
     this EIP describes an improved signature scheme
     that involves chain identifiers.
     [EIP155] lists some chain identifiers, one of which is larger than a byte.
     So we use the library type <see topic='@(url fty::basetypes)'>@('nat')</see>
     for this component of a transaction."))
  ((nonce word)
   (gas-price word)
   (gas-limit word)
   (to maybe-byte-list20)
   (value word)
   (init/data byte-list)
   (sign-v nat)
   (sign-r word)
   (sign-s word))
  :tag :transaction
  :layout :list
  :pred transactionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-encode-transaction ((trans transactionp))
  :returns (mv (error? booleanp)
               (encoding byte-listp))
  :parents (transactions)
  :short "RLP encoding of a transaction."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first step towards RLP-encoding a transaction
     is to turn it into an RLP tree.
     This is implied by [YP:4.2],
     which in fact uses a tuple notation for transactions.")
   (xdoc::p
    "Each scalar component
     is turned into its big-endian byte array representation,
     consistently with @(tsee rlp-encode-scalar).
     Note that here we are just constructing the RLP tree,
     not encoding it yet;
     RLP trees cannot contain scalars.
     The other components are byte arrays that are left unchanged.")
   (xdoc::p
    "We put all nine components under a branching tree,
     which we RLP-encode.
     Encoding may fail,
     if the @($\\mathbf{v}$) signature component is unreasonably large,
     or if the initialization or data array is unreasonably long."))
  (b* (((transaction trans) trans)
       (tree (rlp-tree-branch
              (list (rlp-tree-leaf (nat=>bebytes* trans.nonce))
                    (rlp-tree-leaf (nat=>bebytes* trans.gas-price))
                    (rlp-tree-leaf (nat=>bebytes* trans.gas-limit))
                    (rlp-tree-leaf trans.to)
                    (rlp-tree-leaf (nat=>bebytes* trans.value))
                    (rlp-tree-leaf trans.init/data)
                    (rlp-tree-leaf (nat=>bebytes* trans.sign-v))
                    (rlp-tree-leaf (nat=>bebytes* trans.sign-r))
                    (rlp-tree-leaf (nat=>bebytes* trans.sign-s))))))
    (rlp-encode-tree tree))
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk rlp-transaction-encoding-p ((encoding byte-listp))
  :returns (yes/no booleanp)
  :parents (transactions)
  :short "Check if a byte array is an RLP encoding of a transaction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a declarative, non-executable definition,
     which essentially characterizes the image of @(tsee rlp-encode-transaction)
     (over transaction that can be encoded,
     i.e. such that @(tsee rlp-encode-transaction)
     returns a @('nil') error flag).")
   (xdoc::p
    "By definition,
     the witness function is right inverse of the encoding function,
     over the valid encodings."))
  (exists (transaction)
          (and (transactionp transaction)
               (b* (((mv error? encoding1)
                     (rlp-encode-transaction transaction)))
                 (and (not error?)
                      (equal encoding1 (byte-list-fix encoding))))))
  :skolem-name rlp-transaction-encoding-witness
  ///

  (fty::deffixequiv-sk rlp-transaction-encoding-p
    :args ((encoding byte-listp)))

  (defrule rlp-transactionp-of-rlp-transaction-encoding-witness
    (implies (rlp-transaction-encoding-p encoding)
             (transactionp (rlp-transaction-encoding-witness encoding))))

  (defrule rlp-encode-transaction-of-rlp-transaction-encoding-witness
    (implies (rlp-transaction-encoding-p encoding)
             (b* (((mv error? encoding1)
                   (rlp-encode-transaction
                    (rlp-transaction-encoding-witness encoding))))
               (and (not error?)
                    (equal encoding1
                           (byte-list-fix encoding))))))

  (defrule rlp-transaction-encoding-p-of-rlp-transaction-encode-when-no-error
    (implies (not (mv-nth 0 (rlp-encode-transaction transaction)))
             (rlp-transaction-encoding-p
              (mv-nth 1 (rlp-encode-transaction transaction))))
    :use (:instance rlp-transaction-encoding-p-suff
          (encoding (mv-nth 1 (rlp-encode-transaction
                               (transaction-fix transaction))))
          (transaction (transaction-fix transaction)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlp-decode-transaction ((encoding byte-listp))
  :returns (mv (error? booleanp)
               (transaction
                transactionp
                :hints
                 (("Goal"
                   :in-theory
                   (e/d
                    (rlp-transaction-encoding-p)
                    (rlp-transaction-encoding-p-of-byte-list-fix-encoding))))))
  :parents (transactions)
  :short "RLP decoding of a transaction."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the byte array encodes some transaction, we return that transaction,
     along with a @('nil') error flag.
     Otherwise, we return a @('t') error flag,
     and an irrelevant transaction as second result.")
   (xdoc::p
    "This is a declarative, non-executable definition,
     which says that decoding is the inverse of encoding.
     This is the intention of [YP:4.2], which only specifies encoding,
     leaving decoding implicit.")
   (xdoc::p
    "More precisely, we define decoding as the right inverse of encoding
     (with respect to byte arrays that are valid encodings of transactions),
     as explicated by the theorem
     @('rlp-encode-transaction-of-rlp-decode-transaction').")
   (xdoc::p
    "To prove that decoding is also the left inverse of encoding
     (with respect to encodable transactions),
     we need to prove the injectivity of encoding first;
     this is future work."))
  (b* ((encoding (byte-list-fix encoding)))
    (if (rlp-transaction-encoding-p encoding)
        (mv nil (rlp-transaction-encoding-witness encoding))
      (mv t (transaction 0 0 0 nil 0 nil 0 0 0))))
  :no-function t
  :hooks (:fix)
  ///

  (defrule rlp-encode-transaction-of-rlp-decode-transaction
    (implies (rlp-transaction-encoding-p encoding)
             (b* (((mv d-error? transaction) (rlp-decode-transaction encoding))
                  ((mv e-error? encoding1) (rlp-encode-transaction transaction)))
               (and (not d-error?)
                    (not e-error?)
                    (equal encoding1
                           (byte-list-fix encoding)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-signed-transaction ((nonce wordp)
                                 (gas-price wordp)
                                 (gas-limit wordp)
                                 (to maybe-byte-list20p)
                                 (value wordp)
                                 (init/data byte-listp)
                                 (chain-id natp)
                                 (key secp256k1-priv-key-p))
  :returns (mv (error? (member error? '(nil :rlp :ecdsa)))
               (transaction transactionp))
  :parents (transactions)
  :short "Construction of a signed transaction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This operation is described in [YP:F].
     Two flavors exist, corresponding to the two cases in [YP:(285)]:
     one before and one after the `Spurious Dragon' hard fork "
    (xdoc::ahref "https://github.com/ethereum/EIPs/blob/master/EIPS/eip-155.md"
		 "[EIP155]") ".")
   (xdoc::p
    "In both flavors,
     one starts with the first six components of a @(see transaction):
     nonce,
     gas price,
     gas limit,
     recipient,
     value,
     and initialization/data;
     these are all inputs of this function.
     A tuple is then formed,
     which differs slightly depending on the flavor [YP:(285)]:
     in the ``old'' flavor, the tuple just consists of these six components;
     in the ``new'' flavor, a 9-tuple is formed consisting of
     these six components, a chain id, and two empty byte arrays.
     The 6-tuple is like a partial transaction,
     whose last three components are missing.
     The 9-tuple is like a pre-transaction
     whose last three components contain preliminary values.")
   (xdoc::p
    "The chain id is the seventh input of this function.
     [EIP155] suggests that the chain id is never zero;
     at least, it lists only non-zero chain ids.
     Thus, we use 0 as input to this function to select the old flavor,
     and any non-zero value to select the new flavor;
     we do not constrain the non-zero value
     to be among the chain ids listed in [EIP155].")
   (xdoc::p
    "[YP:(285)] uses the @($v$) result of the ECDSA signature [YP:(279)]
     to distinguish between old and new flavors.
     This is a bit confusing, because the ECDSA signature is calculated
     after forming the tuple, not before.
     The choice of flavor should be determined by external means,
     such as the chain id input of this function.
     (Since we are past the Spurious Dragon hard fork,
     new transactions should always use the new flavor;
     however, this function models the construction of transactions
     before that hard fork as well.)")
   (xdoc::p
    "The tuple notation in [YP:(285)],
     and the fact that the tuples must be hashed,
     suggests that the tuples are in fact RLP trees.
     In the new flavor, the @($()$) in the last two components
     could denote the branching tree with no subtrees,
     but it is more reasonable that it denotes the empty byte array instead.
     This is also consistent with the fact that, in a transaction,
     the last two components are words,
     and that the scalar 0 (which is a reasonable value for the pre-transaction)
     is encoded in the same way as the empty byte array.")
   (xdoc::p
    "The RLP-encoded tuple is hashed with Keccak-256 [YP:F].
     The hash @($e = h(T)$)
     (using the notation in [YP:F], where @($h$) is Keccak-256)
     is passed to the ECDSA signature operation,
     along with a private key that is also an input of this function.
     If the ECDSA signature operation fails,
     the construction of the signed transaction fails;
     this is not explicit in [YP:F].")
   (xdoc::p
    "If the ECDSA signature operation succeeds,
     the resulting @($v$), @($r$), and @($s$) are used
     to construct the last three components of the final signed transaction,
     whose first six components are the same as the first six in
     in the 6-tuple or 9-tuple.
     @($r$) and @($s$) are used directly as the last two components,
     i.e. @($T_\\mathrm{r}$) and @($T_\\mathrm{s}$) [YP:(15)].
     The component @($T_\\mathrm{w}$) depends on the flavor
     (before or after the Spurious Dragon hard fork) [YP:F]:
     in the old flavor, @($T_\\mathrm{w}$) is
     27 if @($v$) indicates an even ephemeral public key y value,
     or 28 if @($v$) indicates odd;
     in the new flavor, @($T_\\mathrm{w}$) is
     the chain identifier doubled plus 35 if @($v$) indicates an even
     ephemeral public key y value, or the chain identifier doubled plus 36
     if @($v$) indicates odd.
     The formulation in [YP:F] suggests that the ECDSA signature operation
     already returns these values as the @($v$) result,
     but these are Ethereum-specific:
     our Ethereum-independent library function for ECDSA signatures
     returns a boolean @($v$), which represents an even ephemeral public key y
     value as @('t') and odd as @('nil').")
   (xdoc::p
    "Besides communicating the chain id, the resulting @($v$) component
     of the signature can be used for public key recovery.
     Based on the discussion in @(tsee secp256k1-sign-det-rec),
     the @('small-x?') flag passed to this signing function must be @('t'),
     so that the parity of the @($y$) coordinate suffices
     to recover the public key.")
   (xdoc::p
    "[YP:(281)] requires the @($s$) component of the signature
     to be below half of the order of the curve.
     Based on the discussion in @(tsee secp256k1-sign-det-rec),
     the @('small-s?') flag passed to this signing function must be @('t'),
     so that an @($s$) suitable for Ethereum is returned.")
   (xdoc::p
    "This function returns the signed transaction as a high-level structure.
     This must be RLP-encoded (via @(tsee rlp-encode-transaction))
     to obtain something that can be sent to the Ethereum network.")
   (xdoc::p
    "This function returns @(':rlp') as the error result if
     the RLP encoding of the 6-tuple or 9-tuple fails.
     If the ECDSA signature operation fails, the error result is @(':ecdsa').
     In both cases, the second result is an irrelevant transaction value."))
  (b* ((nonce (word-fix nonce))
       (gas-price (word-fix gas-price))
       (gas-limit (word-fix gas-limit))
       (to (maybe-byte-list20-fix to))
       (value (word-fix value))
       (6/9-tuple (if (zp chain-id)
                      (rlp-tree-branch
                       (list (rlp-tree-leaf (nat=>bebytes* nonce))
                             (rlp-tree-leaf (nat=>bebytes* gas-price))
                             (rlp-tree-leaf (nat=>bebytes* gas-limit))
                             (rlp-tree-leaf to)
                             (rlp-tree-leaf (nat=>bebytes* value))
                             (rlp-tree-leaf init/data)))
                    (rlp-tree-branch
                     (list (rlp-tree-leaf (nat=>bebytes* nonce))
                           (rlp-tree-leaf (nat=>bebytes* gas-price))
                           (rlp-tree-leaf (nat=>bebytes* gas-limit))
                           (rlp-tree-leaf to)
                           (rlp-tree-leaf (nat=>bebytes* value))
                           (rlp-tree-leaf init/data)
                           (rlp-tree-leaf (nat=>bebytes* chain-id))
                           (rlp-tree-leaf nil)
                           (rlp-tree-leaf nil)))))
       ((mv error? message) (rlp-encode-tree 6/9-tuple))
       ((when error?) (mv :rlp (transaction 0 0 0 nil 0 nil 0 0 0)))
       (hash (keccak-256-bytes message))
       ((mv error? & even? sign-r sign-s) (secp256k1-sign-det-rec hash key t t))
       ((when error?) (mv :ecdsa (transaction 0 0 0 nil 0 nil 0 0 0)))
       (sign-v (if (zp chain-id)
                   (if even? 27 28)
                 (+ (* 2 chain-id) (if even? 35 36)))))
    (mv nil (make-transaction :nonce nonce
                              :gas-price gas-price
                              :gas-limit gas-limit
                              :to to
                              :value value
                              :init/data init/data
                              :sign-v sign-v
                              :sign-r sign-r
                              :sign-s sign-s)))
  :guard-hints (("Goal" :in-theory (enable wordp)))
  :hooks (:fix))
