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
     and a function to RLP-encode them."))
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
   or the empty array (i.e. the only element of @($\\mathbb{B}_0$) [YP:(18)].
   Both [YP:4.2] and [YP:(18)] mention @($\\varnothing$) as
   the (only) element of @($\\mathbb{B}_0$);
   however, according to the definition of @($\\mathbb{B}$) [YP:(178)],
   the empty array should probably be denoted as @($()$).
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
   whether it is initialization code (when the recipient is @('nil')
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
   we pick @('sign-v') (instead of @('sign-w'))
   for the corresponding field name in our product fixtype.
   However, there is an issue with the type of this component:
   [YP:(16)] says that it is a number below 32,
   but [YP:F] says that @($T_{\\mathrm{w}}$) may be
   a chain identifier doubled plus 35 or 36,
   in which case it is above 32.
   It looks like [YP:F] was updated according to EIP 155,
   while [YP:4.2] was not;
   this EIP describes an improved signature scheme
   that involves chain identifiers.
   EIP 155 lists some chain identifiers, one of which is larger than a byte.
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
              (list (rlp-tree-leaf (nat=>bendian* 256 trans.nonce))
                    (rlp-tree-leaf (nat=>bendian* 256 trans.gas-price))
                    (rlp-tree-leaf (nat=>bendian* 256 trans.gas-limit))
                    (rlp-tree-leaf trans.to)
                    (rlp-tree-leaf (nat=>bendian* 256 trans.value))
                    (rlp-tree-leaf trans.init/data)
                    (rlp-tree-leaf (nat=>bendian* 256 trans.sign-v))
                    (rlp-tree-leaf (nat=>bendian* 256 trans.sign-r))
                    (rlp-tree-leaf (nat=>bendian* 256 trans.sign-s))))))
    (rlp-encode-tree tree))
  :no-function t
  :hooks (:fix))
