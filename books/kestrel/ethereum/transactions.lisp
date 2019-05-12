; Ethereum -- Transactions
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

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
  "<p>
   The @($\\mathbf{to}$) field of a transaction [YP:4.2] is
   either a 20-byte (i.e. 160-bit) address
   or the empty array (i.e. the only element of @($\\mathbb{B}_0$)) [YP:(18)].
   Both [YP:4.2] and [YP:(18)] mention @($\\varnothing$) as
   the (only) element of @($\\mathbb{B}_0$);
   however, according to the definition of @($\\mathbb{B}$) [YP:(178)],
   the empty array should be denoted as @($()$).
   </p>
   <p>
   Regardless, in our model the empty byte array is @('nil'),
   so we use either a list of 20 bytes or @('nil')
   to model the @($\\mathbf{to}$) field of a transaction.
   </p>"
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
  "<p>
   A transaction is a 9-tuple [YP:(15)].
   The type of each component is specified in [YP:(16)].
   </p>
   <p>
   We use @(see words) to model natural numbers in @($\\mathbb{N}_{256}$):
   this is the type of the nonce, gas price, gas limit, and value fields.
   </p>
   <p>
   The type of the recipient field is @(tsee maybe-byte-list20).
   See the documentation of that fixtype for details.
   </p>
   <p>
   The sixth component of the tuple is always a byte array,
   whether it is initialization code (when the recipient is @('nil'))
   or it is data (when the recipient is an address).
   </p>
   <p>
   The remaining three components are for the signature.
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
   for this component of a transaction.
   </p>"
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
     is to turn it into an RLP trees.
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
    "We put all nine components under a non-leaf tree,
     which we RLP-encode.
     Encoding may fail,
     if the @($\\mathbf{v}$) signature component is unreasonably large,
     or if the initialization or data array is unreasonably long."))
  (b* (((transaction trans) trans)
       (tree (rlp-tree-nonleaf
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

  (fty::deffixequiv rlp-transaction-encoding-p
    :args ((encoding byte-listp))
    :hints (("Goal"
             :in-theory (disable rlp-transaction-encoding-p-suff)
             :use ((:instance rlp-transaction-encoding-p-suff
                    (transaction
                     (rlp-transaction-encoding-witness
                      (byte-list-fix encoding))))
                   (:instance rlp-transaction-encoding-p-suff
                    (transaction (rlp-transaction-encoding-witness encoding))
                    (encoding (byte-list-fix encoding)))))))

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
