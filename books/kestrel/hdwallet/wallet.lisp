; Cryptocurrency Hierarchical Deterministic Wallet Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HDWALLET")

; Avoid failure for sign in ACL2(r):
; cert_param: non-acl2r

(include-book "kestrel/bitcoin/bip39" :dir :system)
(include-book "kestrel/bitcoin/bip44" :dir :system)
(include-book "kestrel/ethereum/addresses" :dir :system)
(include-book "kestrel/ethereum/transactions" :dir :system)
(include-book "kestrel/utilities/strings/hexstrings" :dir :system)
(include-book "oslib/file-types-logic" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/strtok" :dir :system)

; Added 7/1/2021 by Matt K. after 3 successive ACL2(p) certification failures:
(set-waterfall-parallelism nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ crypto-hdwallet

  :parents (acl2::kestrel-books)

  :short "A hierarchical deterministic wallet for cryptocurrencies."

  :long

  (xdoc::topstring

   (xdoc::h3 "Overview")

   (xdoc::p
    "This wallet is a simple proof of concept:
     it is not meant as a product
     to use with keys that control access to significant assets.
     Nonetheless, due to its formal basis in the ACL2 theorem prover,
     it could serve as a starting point for
     a high-assurance wallet product.")

   (xdoc::p
    "This wallet is meant for use on an air-gapped machine.
     It provides two basic functions: key generation and transaction signing.
     Thus, keys can be generated and used for signing transacions:
     the data of the transaction to sign and the signed transaction
     must be passed between the air-gapped machine where this wallet runs
     and an Internet-connected machine that submits the signed transactions.
     The private keys never leave the air-gapped machine.
     Currently, the wallet does not encrypt these keys, which are stored in
     plaintext in the file system: therefore, the air-gapped machine should
     use disk encryption to protect the keys at rest.
     Currently keys and transactions only for the Ethereum mainnet are supported.")

   (xdoc::p
    "The wallet is hierarchical deterministic, according to "
    (xdoc::seetopic "bitcoin::bip32" "BIP 32")
    ". It uses a mnemonic word sequence according to "
    (xdoc::seetopic "bitcoin::bip39" "BIP 39")
    ". Its internal structure is compliant with "
    (xdoc::seetopic "bitcoin::bip43" "BIP 43")
    " and "
    (xdoc::seetopic "bitcoin::bip44" "BIP 44")
    ".")

   (xdoc::p
    "The wallet can be run by a command line interface shell script
     that runs a Docker image containing the wallet code.
     For details on obtaining, installing, and running the wallet see "
     (xdoc::a
      :href "https://github.com/acl2/acl2/tree/master/books/kestrel/hdwallet/README.md"
      "the README in GitHub")
     ". The following is a technical discussion of the current wallet design.")

   (xdoc::h3 "State")

   (xdoc::p
    "The state of the wallet consists of zero or more private keys
     derived from a seed as in BIP 32.
     The seed is derived from an entropy value, or a corresponding mnemonic,
     as in BIP 39.
     Internally, each key has a path of the form")
   (xdoc::codeblock
    "m / 44' / 60' / 0' / 0 / address_index")
   (xdoc::p
    "where:")
   (xdoc::ul
    (xdoc::li
     "@('44\'') is the BIP 43 purpose index for BIP 44.")
    (xdoc::li
     "@('60\'') is the coin type index for the Ethereum mainnet,
      as prescribed by "
     (xdoc::a
      :href "https://github.com/satoshilabs/slips/blob/master/slip-0044.md"
       "SLIP (Satoshi Labs Improvement Proposal) 44")
     ". This wallet currently supports
      transactions only for the Ethereum mainnet,
      as mentioned above.")
    (xdoc::li
     "@('0\'') is the default account index, according to BIP 44.
      The wallet currently supports only this default account.")
    (xdoc::li
     "@('0') is the external chain index, according to BIP 44.
      For Ethereum, unlike Bitcoin,
      there should be no need for an internal chain index,
      since transactions involve no change back to the payer.")
    (xdoc::li
     "@('address_index') is an address index 0, 1, 2, ...
      Each of these has an associated Ethereum account and address."))
   (xdoc::p
    "Thus, the BIP 32 key tree in the wallet consists of
     a ``line'' from the root key to the external chain key,
     with zero or more children under that.")

   (xdoc::p
    "The state of the wallet also includes a counter
     for the number of address indices used so far.
     This is normally one above the largest address index in the key tree,
     except for the rare cases in which an address key derivation fails
     and that index must be skipped.
     This counter is normally redundant, but not always.")

   (xdoc::h3 "Initialization")

   (xdoc::p
    "The wallet provides two commands to initialize the wallet.
     The first command initializes the wallet
     from an entropy value and a passphrase,
     as described in BIP 39.
     Besides creating the initial key tree (initially without address keys),
     this command also outputs the mnemonic corresponding to the entropy value.
     This may be used by the second initialization command
     to reconstruct (i.e. re-initialize) the wallet,
     from the mnemonic and the passphrase,
     also as described in BIP 39.")

   (xdoc::p
    "It is expected that the user will initially use the first initialization command,
     and use the second initialization command only if and when the wallet must be re-created.
     The wallet currently does not provide facilities
     to generate a securely random entropy:
     the user must use external means for that,
     and pass the entropy to the wallet.")

   (xdoc::p
    "In rare cases, the initialization of the wallet from entropy and passphrase
     may fail, due to the failure to derive some key
     on the ``line'' from the root (master) key to the external chain key.
     In this case, the user must try again
     with a slightly different entropy or passphrase.
     Obviously,
     if a particular entropy and passphrase succeed in creating the wallet
     with the first initialization command,
     then the mnemonic corresponding to that entropy and the same passphrase
     will also succeed in creating the same wallet
     using the second initialization command.")

   (xdoc::h3 "Key Generation")

   (xdoc::p
    "Once the wallet is initialized as explained above,
     the user must create one or more address keys
     in order to sign transactions (see below).
     The wallet provides a command to generate the next address key,
     namely the key whose index is the aforementioned counter
     that is part of the wallet state along with the key tree.
     Since the counter is initially 0,
     the first address key to be generated is the one with index 0,
     then index 1, then index 2, etc.")

   (xdoc::p
    "Normally, the generation of an address key succeeds.
     In this case, besides modifying the internal state of the wallet,
     the command also outputs the index of the key
     (so that the user does not need to keep track of the counter,
     or next index),
     as well as the Ethereum address corresponding to the key.
     The address is derived from the public key
     (as explained in the Ethereum Yellow Paper),
     which is derived from the private key
     (as known in elliptic curve cryptography).")

   (xdoc::p
    "In rare cases, the generation of an address key may fail.
     In this case, the address index is simply skipped,
     and the counter (i.e. next key) is advanced
     so that the command can be tried again to generate the next key.")

   (xdoc::h3 "Transaction Signing")

   (xdoc::p
    "Once at least one address key has been generated
     (normally the one with index 0),
     the command to sign transactions can be used.
     The index of the address key to use for the signature
     is passed to the signing command by the user.")

   (xdoc::p
    "The signing command also takes as inputs
     the following components of the transaction
     (see the Ethereum Yellow Paper for details):")
   (xdoc::ul
    (xdoc::li
     "The nonce associated to the Ethereum address.
      This is stored in the state of the Ethereum network,
      but since this wallet is air-gapped,
      the user must keep track of the nonce,
      and supply it to the signing command.")
    (xdoc::li
     "The gas price for processing the transaction.
      This is under the user's discretion.")
    (xdoc::li
     "The gas limit for processing the transaction.
      This should be accurately estimated by the user,
      plausibly with the aid of some tools external to the wallet.")
    (xdoc::li
     "The recipient address.
      The address may be that of a contract
      or of an externally owned account;
      the wallet supports both.")
    (xdoc::li
     "The value to transmit to the recipient, in Wei.")
    (xdoc::li
     "The data (a sequence of bytes) to pass to the recipient.
      This makes sense when the recipient is a contract,
      as opposed to an externally owned account."))

   (xdoc::p
    "The command outputs the bytes of the signed transaction, RLP-encoded.
     This is the form in which the transaction
     must be submitted to the Ethereum network.
     Since this wallet is air-gapped,
     the user must copy the output of this command
     and use an Internet-connected machine
     to actually submit the transaction.")

   (xdoc::p
    "In rare cases, the signing of the transaction may fail.
     Since the elliptic curve signature scheme used by this wallet
     is deterministic,
     re-trying the same command will fail again.
     Instead, the user could try to change slightly
     some non-critical component of the transaction,
     such as the gas limit.")

   (xdoc::h3 "Persistence")

   (xdoc::p
    "This wallet runs in ``batch'' mode:
     each command starts up the wallet,
     which terminates at the end of the command.
     The state of the wallet must be therefore stored persistently,
     in a file in the file system.
     The ACL2 constant @(tsee *stat-filepath*) holds the path to this file:
     it is currently set to a relative path in this directory,
     but it can be easily changed of course.")

   (xdoc::p
    "Currently the file stores the wallet state in plaintext,
     i.e. not encrypted.
     Future versions of the wallet will likely use AES encryption.
     However, recall that this wallet is meant for an air-gapped machine:
     at rest, the wallet state can be protected by disk encryption.
     Thus, even if the machine is stolen,
     it should not be possible to recover the wallet state,
     assuming that the disk encryption is protected by a  strong password.")

   (xdoc::h3 "Error Handling")

   (xdoc::p
    "The wallet carefully validates all the user inputs
     and provides informative error messages when the inputs are invalid.
     The wallet also provides informative error messages
     when some internal cryptographic operation fails
     due to a rare but possible event (as mentioned above).
     There is just one exception to this approach to error handling:
     in order to load/save the wallet state from/to the file,
     the wallet implementation uses ACL2's
     @(tsee serialize-read) and @(tsee serialize-write),
     which may throw hard errors in some cases.
     Thus, it is currently possible, but hopefully rare,
     to get an ACL2 hard error from the wallet."))

  :order-subtopics t

  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod stat
  :short "State of the wallet."
  :long
  (xdoc::topstring
   (xdoc::p
    "The state of the wallet includes a BIP 32 key tree.")
   (xdoc::p
    "The key tree will always include:
     the purpose key (44') just under the root key;
     the Ethereum mainnet coin type key (60') just under that;
     the default account key (0') just under that;
     the external chain key (0) just under that;
     and 0 or more address keys just under that.
     In rare cases, some address key may be missing
     (when their derivation fails);
     see BIP 32 for details.
     Thus, every key in the tree
     is identified by a path of the following form:")
   (xdoc::codeblock
    "m / 44' / 60' / 0' / 0 / address_index")
   (xdoc::p
    "The state of the wallet also includes
     the number of address keys derived so far.
     More precisely, this is the number of address keys
     attempted to derive so far,
     since in rare cases key derivation may fail (see BIP 32).")
   (xdoc::p
    "Because of this rare eventuality,
     this additional state component (the number of addresses)
     is not always redundant with the key tree,
     i.e. it cannot always be derived from the key tree.
     For example, the user may have attempted to derive 10 address keys,
     with indices 0 to 9, all of which were successful
     except for the one with index 9.
     Then the key tree would have 9 address keys (with indices 0 to 8),
     and no key for index 9.
     However, the additional state component for the number of addresses
     would be 10 in this case, and not 9.
     In this way, the next address key derivation attempt can be made
     at index 10, and not again at index 9 (which would fail again).")
   (xdoc::p
    "This fixtype captures the basic structure of the state of the wallet.
     Additional constraints, including the ones outlined above,
     are expressed by the well-formedness predicate @(tsee stat-wfp)."))
  ((keys bip32-key-tree)
   (addresses nat))
  :tag :state
  :layout :list
  :pred statp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-stat
  stat
  :pred maybe-statp
  :short "Union of wallet states and @('nil').")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-addresses-bounded-p ((stat statp))
  :returns (yes/no booleanp)
  :short "Constraint on the number of address keys in the wallet state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since all the address keys have non-hardened indices,
     the largest index is @($2^{31}-1$),
     so the maximum value of the @('addresses') state component
     is @($2^{31}$)."))
  (<= (stat->addresses stat)
      (expt 2 31))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-priv-keys-p ((stat statp))
  :returns (yes/no booleanp)
  :short "Constraint on the kind of keys in the wallet state."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the keys in the key tree are private,
     because we create a private master key
     and then all the derived keys are private."))
  (bip32-key-tree-priv-p (stat->keys stat))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-root-depth-zero-p ((stat statp))
  :returns (yes/no booleanp)
  :short "Constraint on the root depth in the wallet state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The key tree is rooted at the master key, which has depth 0."))
  (equal (bip32-key-tree->root-depth (stat->keys stat))
         0)
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *purpose-index*
  :short "The purpose index of the paths to the address keys of the wallet."
  :long (xdoc::topstring-p "This is the index @('44\'').")
  (+ *bip44-purpose* (expt 2 31))
  ///
  (assert-event (ubyte32p *purpose-index*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *coin-type-index*
  :short "The coin type index of the paths to the address keys of the wallet."
  :long
  (xdoc::topstring-p
   "This is the index @('60\''), for the Ethereum mainnet.")
  (+ 60 (expt 2 31))
  ///
  (assert-event (ubyte32p *coin-type-index*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *account-index*
  :short "The account index of the paths to the address keys of the wallet."
  :long (xdoc::topstring-p "This is the index @('0\'').")
  (expt 2 31)
  ///
  (assert-event (ubyte32p *account-index*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *external-chain-index*
  :short "The external chain index of the paths to
          the address keys of the wallet."
  :long (xdoc::topstring-p "This is the index @('0').")
  0
  ///
  (assert-event (ubyte32p *external-chain-index*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *key-path-prefix*
  :short "The prefix of the path to the address keys of the wallet."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every address key in the wallet is identified
     by a path that starts with the indices of the
     purpose,
     (Ethereum mainnet) coin type,
     (default) account,
     and (external) chain
     keys.
     This constant captures this prefix path."))
  (list *purpose-index*
        *coin-type-index*
        *account-index*
        *external-chain-index*)
  ///

  (assert-event (ubyte32-listp *key-path-prefix*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-path-prefix-in-tree-p ((stat statp))
  :returns (yes/no booleanp)
  :short "Constraint on the key path prefix in the wallet state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The prefix of the address keys is always in the key tree."))
  (bip32-path-in-tree-p *key-path-prefix* (stat->keys stat))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-key-path-p ((path ubyte32-listp) (addresses natp))
  :returns (yes/no booleanp)
  :short "Check if a key path is valid for the wallet."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the key paths in the wallet must have the form")
   (xdoc::codeblock
    "m / 44' / 60' / 0' / 0 / address_index")
   (xdoc::p
    "where @('address_index') is less than the @('addresses') state component,
     or they may be prefixes of that;
     BIP 32 key trees are always required to be closed under prefixes.")
   (xdoc::p
    "This predicate checks if a path has one of these forms."))
  (b* (((when (atom path)) t)
       ((unless (= (car path) *purpose-index*)) nil)
       (path (cdr path))
       ((when (atom path)) t)
       ((unless (= (car path) *coin-type-index*)) nil)
       (path (cdr path))
       ((when (atom path)) t)
       ((unless (= (car path) *account-index*)) nil)
       (path (cdr path))
       ((when (atom path)) t)
       ((unless (= (car path) *external-chain-index*)) nil)
       (path (cdr path))
       ((when (atom path)) t)
       ((unless (< (car path) addresses)) nil)
       (path (cdr path)))
    (atom path))
  :no-function t
  ///

  (defrule valid-key-path-p-of-next-key-path-under-1+-addresses
    (valid-key-path-p (rcons addresses *key-path-prefix*) (1+ addresses))
    :enable rcons)

  (defrule valid-key-path-p-of-1+-addresses
    (implies (valid-key-path-p path addresses)
             (valid-key-path-p path (1+ addresses)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-valid-key-paths-p ((paths bip32-path-setp)
                               (addresses natp))
  :returns (yes/no booleanp)
  :short "Lift @(tsee valid-key-path-p) to sets of paths."
  (or (empty paths)
      (and (valid-key-path-p (head paths) addresses)
           (all-valid-key-paths-p (tail paths) addresses)))
  :no-function t
  ///

  (defrule valid-key-path-p-when-member-and-all-valid-key-paths-p
    (implies (and (in path paths)
                  (all-valid-key-paths-p paths addresses))
             (valid-key-path-p path addresses)))

  (defrule all-valid-key-paths-p-of-insert
    (equal (all-valid-key-paths-p (insert path paths) addresses)
           (and (valid-key-path-p path addresses)
                (all-valid-key-paths-p paths addresses))))

  (defrule all-valid-key-paths-p-of-1+-addresses
    (implies (all-valid-key-paths-p paths addresses)
             (all-valid-key-paths-p paths (1+ addresses))))

  (defrule not-all-valid-key-paths-p-of-next-key-path
    (implies (all-valid-key-paths-p paths addresses)
             (not (in (rcons addresses *key-path-prefix*) paths)))
    :enable (valid-key-path-p rcons)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-all-valid-key-paths-p ((stat statp))
  :returns (yes/no booleanp)
  :short "Check if all the key paths in the wallet are valid."
  (all-valid-key-paths-p (bip32-key-tree->index-tree (stat->keys stat))
                         (stat->addresses stat))
  :no-function t
  ///

  (defrule not-bip32-path-in-tree-p-of-next-key-path
    (implies (and (stat-addresses-bounded-p stat)
                  (stat-all-valid-key-paths-p stat))
             (not (bip32-path-in-tree-p
                   (rcons (stat->addresses stat) *key-path-prefix*)
                   (stat->keys stat))))
    :enable (stat-addresses-bounded-p
             bip32-path-in-tree-p
             ubyte32-fix
             ubyte32p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-wfp ((stat statp))
  :returns (yes/no booleanp)
  :short "All the constraints on the wallet state."
  (and (stat-addresses-bounded-p stat)
       (stat-priv-keys-p stat)
       (stat-root-depth-zero-p stat)
       (stat-path-prefix-in-tree-p stat)
       (stat-all-valid-key-paths-p stat))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *stat-filepath*
  :short "Path of the file that stores the state of the wallet."
  :long
  (xdoc::topstring
   (xdoc::p
    "For this open-source wallet code,
     this is set to a file in the current directory
     (where the code also resides).
     To create a standalone wallet application,
     this can be changed to some other (perhaps absolute) path."))
  "wallet-state")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *command-name-init-from-entropy*
  :short "Name of the command to initialize the wallet from an entropy value."
  "init-from-entropy"
  ///
  (assert-event (stringp *command-name-init-from-entropy*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *command-name-init-from-mnemonic*
  :short "Name of the command to initialize the wallet from a mnemonic."
  "init-from-mnemonic"
  ///
  (assert-event (stringp *command-name-init-from-mnemonic*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *command-name-sign*
  :short "Name of the command to sign a transaction."
  "sign"
  ///
  (assert-event (stringp *command-name-sign*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *command-name-next-key*
  :short "Name of the command to generate the next key."
  "next-key"
  ///
  (assert-event (stringp *command-name-next-key*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum command-error
  :short "Possible command errors."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are structured error values
     that may be returned by the functions
     that model the commands of the wallet.")
   (xdoc::p
    "Some are directly associated to command inputs (strings)
     that are incorrect in some ways.
     Others arise when more internal processes (such as key derivations) fail.
     The meaning of these errors is explained
     in the documentation of the functions that may return them.
     One arises if the file that stores the wallet state has been corrupted."))
  (:malformed-mnemonic ((mnemonic string)))
  (:malformed-passphrase ((passphrase string)))
  (:malformed-entropy ((entropy string)))
  (:malformed-nonce ((nonce string)))
  (:malformed-gas-price ((gas-price string)))
  (:malformed-gas-limit ((gas-limit string)))
  (:malformed-to ((to string)))
  (:malformed-value ((value string)))
  (:malformed-data ((data string)))
  (:malformed-address-key-index ((address-key-index string)))
  (:address-key-index-too-large ((address-key-index nat) (limit nat)))
  (:address-key-index-skipped ((address-key-index nat)))
  (:root-key-derivation-fail ())
  (:purpose-key-derivation-fail ())
  (:coin-type-key-derivation-fail ())
  (:account-key-derivation-fail ())
  (:external-chain-key-derivation-fail ())
  (:address-key-derivation-fail ((address-key-index nat)))
  (:address-key-index-limit ())
  (:pretransaction-rlp-fail ())
  (:transaction-sign-fail ())
  (:transaction-rlp-fail ())
  (:state-file-untestable ())
  (:state-file-absent ())
  (:state-file-present ())
  (:state-file-not-regular ())
  (:state-file-malformed ())
  (:wrong-number-of-arguments ((required nat) (given nat)))
  (:wrong-command ((command stringp)))
  (:no-command ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-command-error
  command-error
  :short "Union of command errors and @('nil').")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define command-error-message ((command stringp) (error command-error-p))
  :returns (msg msgp)
  :short "Turn a command error into a user-oriented message."
  :long
  (xdoc::topstring
   (xdoc::p
    "The message consists of two parts:")
   (xdoc::ol
    (xdoc::li
     "A heading that indicates that an error has occurred,
      and the command in which it occurred (if applicable).")
    (xdoc::li
     "A body that describes the error that occurred.
      This is separated by a blank line from the heading.")))
  (b* ((heading-core (if (member-equal command
                                       (list *command-name-init-from-entropy*
                                             *command-name-init-from-mnemonic*
                                             *command-name-sign*
                                             *command-name-next-key*))
                         (msg "Error in command '~s0':" command)
                       (msg "Error:")))
       (heading (msg "~@0~%~%" heading-core))
       (body-core
        (command-error-case
         error
         :malformed-mnemonic
          (msg "The supplied mnemonic argument is impossibly long: ~
                it consists of ~x0 characters."
               (length error.mnemonic))
         :malformed-passphrase
          (msg "The supplied passphrase argument is impossibly long: ~
                it consists of ~x0 characters."
               (length error.passphrase))
         :malformed-entropy
          (msg "The entropy argument must be a sequence of ~
                32, 40, 48, 56, or 64 hexadecimal digits without spaces ~
                (forming a sequence of 16, 20, 24, 28, or 32 bytes).
                The supplied entropy argument~%~%~
                ~s0~s1~%~%~
                does not have that form."
               "  " error.entropy)
         :malformed-nonce
          (msg "The nonce argument must be a sequence of ~
                decimal digits without spaces that form a 256-bit number. ~
                The supplied nonce argument~%~%~
                ~s0~s1~%~%~
                does not have that form."
               "  " error.nonce)
         :malformed-gas-price
          (msg "The gas price argument must be a sequence of ~
                decimal digits without spaces that forms a 256-bit number. ~
                The supplied gas price argument~%~%~
                ~s0~s1~%~%~
                does not have that form."
               "  " error.gas-price)
         :malformed-gas-limit
          (msg "The gas limit argument must be a sequence of ~
                decimal digits without spaces that forms a 256-bit number. ~
                The supplied gas limit argument~%~%~
                ~s0~s1~%~%~
                does not have that form."
               "  " error.gas-limit)
         :malformed-to
          (msg "The recipient argument must be a sequence of ~
                40 hexadecimal digits without spaces ~
                (forming a sequence of 20 bytes).
                The supplied recipient argument~%~%~
                ~s0~s1~%~%~
                does not have that form."
               "  " error.to)
         :malformed-value
          (msg "The value argument must be a sequence of ~
                decimal digits without spaces that form a 256-bit number. ~
                The supplied value argument~%~%~
                ~s0~s1~%~%~
                does not have that form."
               "  " error.value)
         :malformed-data
          (msg "The data argument must be a sequence of ~
                an even number of hexadecimal digits without spaces ~
                (forming a sequence of bytes of half the length). ~
                The supplied data argument~%~%~
                ~s0~s1~%~%~
                does not have that form."
               "  " error.data)
         :malformed-address-key-index
          (msg "The address key index argument must be a sequence of ~
                decimal digits without spaces that form a number. ~
                The supplied address key index argument~%~%~
                ~s0~s1~%~%~
                does not have that form."
               "  " error.address-key-index)
         :address-key-index-too-large
          (msg "The address key index argument ~x0 ~
                must denote an existing key, ~
                i.e. it must be a number between ~
                0 (inclusive) and ~x1 (exclusive), ~
                where ~x1 is the number of address key indices used so far."
               error.address-key-index error.limit)
         :address-key-index-skipped
          (msg "The address key index argument ~x0 ~
                must denote an existing key, ~
                but the derivation of the address key with that index failed ~
                and therefore the key with that index was skipped."
               error.address-key-index)
          :root-key-derivation-fail
          (msg "The derivation of the root key from the seed ~
                failed, and therefore the wallet cannot be initialized. ~
                This is rare, but not impossible.
                Try initializing the wallet again with different inputs, ~
                perhaps just a different passphrase: ~
                this will generally produce a different seed.")
         :purpose-key-derivation-fail
          (msg "The derivation of the purpose key from the root key ~
                failed, and therefore the wallet cannot be initialized. ~
                This is rare, but not impossible.
                Try initializing the wallet again with different inputs, ~
                perhaps just a different passphrase: ~
                this will generally produce a different seed ~
                and therefore a different ~
                root key.")
         :coin-type-key-derivation-fail
          (msg "The derivation of the coin type key from the purpose key ~
                failed, and therefore the wallet cannot be initialized. ~
                This is rare, but not impossible.
                Try initializing the wallet again with different inputs, ~
                perhaps just a different passphrase: ~
                this will generally produce a different seed ~
                and therefore a different ~
                root key and purpose key.")
         :account-key-derivation-fail
          (msg "The derivation of the account key from the coin type key ~
                failed, and therefore the wallet cannot be initialized. ~
                This is rare, but not impossible.
                Try initializing the wallet again with different inputs, ~
                perhaps just a different passphrase: ~
                this will generally produce a different seed ~
                and therefore a different ~
                root key, purpose key, and coin type key.")
         :external-chain-key-derivation-fail
          (msg "The derivation of the external chain key from the account key ~
                failed, and therefore the wallet cannot be initialized. ~
                This is rare, but not impossible.
                Try initializing the wallet again with different inputs, ~
                perhaps just a different passphrase: ~
                this will generally produce a different seed ~
                and therefore a different ~
                root key, purpose key, coin type key, and account key.")
         :address-key-derivation-fail
          (msg "The derivation of the address key with index ~x0 failed. ~
                This is rare, but not impossible.
                This address key index will be marked as skipped.
                Run this command again to attempt to derive an address key ~
                with the next index."
               error.address-key-index)
         :address-key-index-limit
          (msg "A very large number of address keys ~
                has already been generated in this wallet, ~
                reaching the maximum address key index ~x0. ~
                Therefore, it is not possible to generate another key, ~
                because its index would exceed the maximum. ~
                Try creating an additional wallet."
               (1- (expt 2 31)))
         :pretransaction-rlp-fail
          (msg "An impossibly large transaction is being created for signing. ~
                It is so large that it cannot be RLP-encoded, ~
                which is required in order to sign it.")
         :transaction-sign-fail
          (msg "The ECDSA signature of the transaction failed. ~
                This is rare but not impossible. ~
                Since this wallet uses a deterministic ECDSA, ~
                attempting to create the same transaction will fail again. ~
                Try instead varying slightly ~
                some non-critical components of the transaction, ~
                such as the gas limit.")
         :transaction-rlp-fail
          (msg "An impossibly large signed transaction has been created. ~
                It is so large that it cannot be RLP-encoded, ~
                which is required in order to send it to the Ethereum network.")
         :state-file-untestable
          (msg "A failure occurred while attempting to check ~
                whether a file with the wallet state exists. ~
                This is out of the wallet's control. ~
                Make sure that the directory (and file, if it exists) ~
                are accessible to the user who is running the wallet: ~
                the path of the file is '~s0'."
               *stat-filepath*)
         :state-file-absent
          (msg "No file with the wallet state was found at the path '~s0'. ~
                This command requires that file to exist, ~
                i.e. that the wallet has already been initialized."
               *stat-filepath*)
         :state-file-present
          (msg "A file with the wallet state was found at the path '~s0'. ~
                This command will overwrite that file. ~
                If that is intended, separately remove the file ~
                and try this command again."
               *stat-filepath*)
         :state-file-not-regular
          (msg "The path '~s0' to the wallet state exists in the file system, ~
                but it does not refer to a regular file. ~
                The file system entity at that path
                may have been modified from outside the wallet. ~
                Re-create the file by re-initializing the wallet ~
                from the original mnemonic and passphrase."
               *stat-filepath*)
         :state-file-malformed
          (msg "The file at the path '~s0' does not contain ~
                a well-formed wallet state. ~
                The file may have been modified from outside the wallet. ~
                Re-create the file by re-initializing the wallet ~
                from the original mnemonic and passphrase."
               *stat-filepath*)
         :wrong-number-of-arguments
          (msg "This command requires ~x0 arguments,
                but ~x1 arguments were supplied instead."
               error.required error.given)
         :wrong-command
          (msg "The supplied command '~s0' is not among the wallet commands. ~
                The wallet commands are '~s1', '~s2', '~s3', and '~s4'."
               command
               *command-name-init-from-entropy*
               *command-name-init-from-mnemonic*
               *command-name-sign*
               *command-name-next-key*)
         :no-command
          (msg "No command was supplied to the wallet. ~
                The wallet commands are '~s0', '~s1', '~s2', and '~s3'."
               *command-name-init-from-entropy*
               *command-name-init-from-mnemonic*
               *command-name-sign*
               *command-name-next-key*)))
       (body (msg "~@0~%~%" body-core)))
    (msg "~@0~@1" heading body))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-to-byte-list ((string stringp))
  :returns (mv (error? booleanp)
               (bytes
                byte-listp
                :hints (("Goal"
                         :in-theory
                         (enable
                          acl2::byte-listp-rewrite-unsigned-byte-listp)))))
  :short "Parse a string into a list of bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Certain wallet commands take byte lists as inputs,
     which are supplied by the wallet's user as strings.
     These must be an even-length strings of hexadecimal digits,
     where the letters may be uppercase or lowercase.
     Each pair of hexadecimal digits is turned into a byte,
     with the first digit becoming the most significant nibble of the byte.
     If the string cannot be converted to a byte list,
     the error result is @('t')."))
  (if (and (stringp string)
           (hex-digit-string-p string)
           (evenp (length string)))
      (mv nil (hexstring=>ubyte8s string))
    (mv t nil))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-to-nat ((string stringp))
  :returns (mv (error? booleanp)
               (nat natp))
  :short "Parse a string into a natural number."
  :long
  (xdoc::topstring
   (xdoc::p
    "Certain wallet commands take natural numbers as inputs,
     which are supplied by the wallet's user as strings.
     These must be non-empty sequences of decimal digits,
     which are turned into their big-endian value.
     If the string cannot be converted to a natural number,
     the error result is @('t')."))
  (b* ((val (strval string))
       ((when (null val)) (mv t 0)))
    (mv nil val))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-to-word ((string stringp))
  :returns (mv (error? booleanp)
               (word wordp))
  :short "Parse a string into a word."
  :long
  (xdoc::topstring
   (xdoc::p
    "Certain wallet commands take words (in the Ethereum sense) as inputs,
     which are supplied by the wallet's user as strings.
     These must be non-empty sequences of decimal digits,
     which are turned into their big-endian value.
     If the string cannot be converted to a word,
     the error result is @('t')."))
  (b* (((mv error? val) (string-to-nat string))
       ((when error?) (mv error? 0))
       ((unless (wordp val)) (mv t 0)))
    (mv nil val))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-from-mnemonic ((mnemonic stringp) (passphrase stringp))
  :returns (mv (error? maybe-command-error-p)
               (stat? maybe-statp))
  :short "Initialization of the wallet from a mnemonic (and passphrase)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This models the command used to initialize the wallet
     from a mnemonic (and a passphrase).
     This may be used to port the keys from another wallet,
     as opposed to creating a new wallet from scratch
     via @(tsee init-from-entropy).")
   (xdoc::p
    "This initialization function takes two strings as inputs,
     the first of which should be
     a space-separated sequence of BIP 39 mnemonic words;
     however, we do not check that it is,
     because, as noted in @(tsee bip39-mnemonic-to-seed),
     the seed derivation works for any string.
     The two input strings are converted to a BIP 32 seed,
     from which the master key is derived.
     The master key determines the initial key tree.")
   (xdoc::p
    "We also immediately derive
     the purpose key 44',
     the Ethereum mainnet coin type key 60',
     the default account key 0',
     and the external chain key 0;
     see @(tsee stat).
     We set the number of address keys to 0 initially,
     i.e. we do not (attempt to) derive any address key yet.")
   (xdoc::p
    "The derivation of the master key, or of the other keys mentioned above,
     may fail.
     This is rare, but not impossible.
     In this case, initialization fails,
     as signaled by this function returning an error as the first result
     (and @('nil') as second result).")
   (xdoc::p
    "If this initialization operation succeeds,
     the initial state of the wallet satisfies
     all the constraints formalized by @(tsee stat-wfp).")
   (xdoc::p
    "Errors are returned if the mnemonic or passphrase strings
     are unreasonably large.
     Such large strings are virtually impossible to type,
     but we need the check to ensure that
     the guards of the involved cryptographic functions are satisfied."))
  (b* (((unless (< (length mnemonic) (expt 2 125)))
        (mv (command-error-malformed-mnemonic mnemonic) nil))
       ((unless (< (length passphrase) (- (expt 2 125) (+ 128 4 8))))
        (mv (command-error-malformed-passphrase passphrase) nil))
       (seed (bip39-mnemonic-to-seed mnemonic passphrase))
       ((mv error? tree) (bip32-master-tree seed))
       ((when error?)
        (mv (command-error-root-key-derivation-fail) nil))
       (path nil)
       (next *purpose-index*)
       ((mv error? tree) (bip32-extend-tree tree path next))
       ((when error?)
        (mv (command-error-purpose-key-derivation-fail) nil))
       (path (rcons next path))
       (next *coin-type-index*)
       ((mv error? tree) (bip32-extend-tree tree path next))
       ((when error?)
        (mv (command-error-coin-type-key-derivation-fail) nil))
       (path (rcons next path))
       (next *account-index*)
       ((mv error? tree) (bip32-extend-tree tree path next))
       ((when error?)
        (mv (command-error-account-key-derivation-fail) nil))
       (path (rcons next path))
       (next *external-chain-index*)
       ((mv error? tree) (bip32-extend-tree tree path next))
       ((when error?)
        (mv (command-error-external-chain-key-derivation-fail) nil)))
    (mv nil (stat tree 0)))
  :guard-hints (("Goal" :in-theory (enable bip32-path-in-tree-p)))
  :no-function t
  ///

  (defrule statp-of-init-from-mnemonic-when-no-error
    (b* (((mv error? stat?) (init-from-mnemonic mnemonic passphrase)))
      (implies (not error?)
               (statp stat?))))

  (defrule stat-wfp-of-init-from-mnemonic-when-no-error
    (b* (((mv error? stat?) (init-from-mnemonic mnemonic passphrase)))
      (implies (not error?)
               (stat-wfp stat?)))
    :enable (stat-wfp
             stat-addresses-bounded-p
             stat-priv-keys-p
             stat-root-depth-zero-p
             stat-path-prefix-in-tree-p
             bip32-path-in-tree-p
             stat-all-valid-key-paths-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-from-entropy ((entropy-string stringp) (passphrase stringp))
  :returns (mv (error? maybe-command-error-p)
               (mnemonic stringp)
               (stat? maybe-statp))
  :short "Initialization of the wallet from an entropy value
          (and a passphrase)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This models the command used to initialize the wallet
     from an entropy value (and a passphrase).
     This may be used to create a new wallet from scratch,
     as opposed to porting the keys from another wallet
     via @(tsee init-from-mnemonic).")
   (xdoc::p
    "The entropy is supplied as a hex string (see @(tsee string-to-byte-list)).
     After turning the string into a list of bytes and then a list of bits,
     we turn the resulting entropy into a mnemonic,
     and then we call @(tsee init-from-mnemonic)
     to initialize the wallet from the generated mnemonic.")
   (xdoc::p
    "Besides the initial wallet state,
     we also return the generated mnemonic,
     so that the user can make a note of it and store it securely.
     The mnemonic can be later used by the user to re-create the wallet,
     via @(tsee init-from-mnemonic).")
   (xdoc::p
    "The first result is an error flag.
     It is set exactly when
     the input entropy string is malformed,
     or the creation of the initial state from the mnemonic fails
     (see @(tsee init-from-mnemonic)).")
   (xdoc::p
    "If this initialization operation succeeds,
     the initial state of the wallet satisfies
     all the constraints formalized by @(tsee stat-wfp)."))
  (b* (((mv error? entropy-bytes) (string-to-byte-list entropy-string))
       ((when error?)
        (mv (command-error-malformed-entropy entropy-string) "" nil))
       (entropy (bebytes=>bits entropy-bytes))
       ((unless (bip39-entropy-size-p (len entropy)))
        (mv (command-error-malformed-entropy entropy-string) "" nil))
       (mnemonic (bip39-entropy-to-mnemonic entropy))
       ((unless (< (length passphrase) (- (expt 2 125) (+ 128 4 8))))
        (mv (command-error-malformed-passphrase passphrase) "" nil))
       ((mv error? stat) (init-from-mnemonic mnemonic passphrase))
       ((when error?)
        (mv error? "" nil)))
    (mv nil mnemonic stat))
  :guard-hints (("Goal" :in-theory (enable bip39-entropyp
                                           bip39-entropy-size-p)))
  :no-function t
  ///

  (defrule statp-of-init-from-entropy-when-no-error
    (b* (((mv error? & stat?) (init-from-entropy entropy passphrase)))
      (implies (not error?)
               (statp stat?))))

  (defrule stat-wfp-of-init-from-entropy-when-no-error
    (b* (((mv error? & stat?) (init-from-entropy entropy passphrase)))
      (implies (not error?)
               (stat-wfp stat?)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sign ((nonce-string stringp)
              (gas-price-string stringp)
              (gas-limit-string stringp)
              (to-string stringp)
              (value-string stringp)
              (data-string stringp)
              (address-key-index-string stringp)
              (stat statp))
  :guard (stat-wfp stat)
  :returns (mv (error? maybe-command-error-p)
               (signed-transaction byte-listp))
  :short "Transaction signature in the wallet."
  :long
  (xdoc::topstring
   (xdoc::p
    "This models the command used
     to sign a transaction with a key in the wallet.")
   (xdoc::p
    "In Ethereum, a transaction is a 9-tuple, as formalized "
    (xdoc::seetopic "ethereum::transaction" "here")
    ". The first six components are inputs of this function:
     nonce, gas price, gas limit, recipient, value, and data.
     For now, we do not support contract creation transactions;
     thus, the sixth component is always data bytes, not initialization bytes.
     The other three components are the signature,
     which this function calculates.")
   (xdoc::p
    "The address key to use is specified by another input of this function.
     This index is used to retrieve the key from the state.
     The index must be below the number of address keys generated so far,
     otherwise an error saying that the index is too large is returned.
     In addition, the index must correspond to an existing key,
     one whose derivation has not failed;
     otherwise an error saying that the key was skipped was returned.")
   (xdoc::p
    "We construct a signed transaction with chain id 1,
     which is for the Ethereum mainnet.
     We return the RLP encoding of that transaction.")
   (xdoc::p
    "The guard proofs of this operation need some of the constraints
     formalized in @(tsee stat-wfp).")
   (xdoc::p
    "Since this operation does not change the (and does not return a) state,
     it trivially preserves the state constraints @(tsee stat-wfp).")
   (xdoc::p
    "The six components of the transaction are passed as string inputs,
     which we parse and validate.
     Is validation fails, specific error values are returned."))
  (b* (((mv error? nonce) (string-to-word nonce-string))
       ((when error?)
        (mv (command-error-malformed-nonce nonce-string) nil))
       ((mv error? gas-price) (string-to-word gas-price-string))
       ((when error?)
        (mv (command-error-malformed-gas-price gas-price-string) nil))
       ((mv error? gas-limit) (string-to-word gas-limit-string))
       ((when error?)
        (mv (command-error-malformed-gas-limit gas-limit-string) nil))
       ((mv error? to) (string-to-byte-list to-string))
       ((when (or error?
                  (not (= (len to) 20))))
        (mv (command-error-malformed-to to-string) nil))
       ((mv error? value) (string-to-word value-string))
       ((when error?)
        (mv (command-error-malformed-value value-string) nil))
       ((mv error? data) (string-to-byte-list data-string))
       ((when error?)
        (mv (command-error-malformed-data data-string) nil))
       ((mv error? address-key-index) (string-to-nat address-key-index-string))
       ((when error?)
        (mv (command-error-malformed-address-key-index address-key-index-string)
            nil))
       ((unless (< address-key-index (stat->addresses stat)))
        (mv (command-error-address-key-index-too-large address-key-index
                                                       (stat->addresses stat))
            nil))
       ((unless (bip32-path-in-tree-p
                 (rcons address-key-index *key-path-prefix*)
                 (stat->keys stat)))
        (mv (command-error-address-key-index-skipped address-key-index) nil))
       (path (rcons address-key-index *key-path-prefix*))
       (key (bip32-get-priv-key-at-path (stat->keys stat) path))
       (chain-id 1)
       ((mv error? transaction) (make-signed-transaction nonce
                                                         gas-price
                                                         gas-limit
                                                         to
                                                         value
                                                         data
                                                         chain-id
                                                         key))
       ((when (eq error? :rlp))
        (mv (command-error-pretransaction-rlp-fail) nil))
       ((when (eq error? :ecdsa))
        (mv (command-error-transaction-sign-fail) nil))
       ((mv error? transaction-rlp) (rlp-encode-transaction transaction))
       ((when error?)
        (mv (command-error-transaction-rlp-fail) nil)))
    (mv nil transaction-rlp))
  :guard-hints (("Goal" :in-theory (enable stat-wfp
                                           stat-addresses-bounded-p
                                           stat-priv-keys-p
                                           ubyte32p
                                           maybe-byte-list20p
                                           byte-list20p)))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define next-key ((stat statp))
  :returns (mv (error? maybe-command-error-p)
               (index natp)
               (address byte-list20p)
               (stat statp))
  :guard (stat-wfp stat)
  :short "Address key generation in the wallet."
  :long
  (xdoc::topstring
   (xdoc::p
    "This models the command used
     to generate the next address key in the wallet.")
   (xdoc::p
    "We attempt to derive the address key whose index is
     the state component that counts the number of
     (attempted) address key derivations so far.")
   (xdoc::p
    "This may fail in two rare cases.
     One is the case in which key derivation fails,
     as discussed in [BIP32].
     The other is the case in which
     the index of the next address key is @($2^{31}$):
     since according to [BIP44] address keys are not hardened,
     their indices are limited to the set @($[0,2^{31})$).
     In the first case,
     this function returns @(':address-key-derivation-failed')
     as the error flag.
     In the second case,
     this function returns @(':address-key-index-too-large')
     as the error flag.
     In all the other cases, the error flag is @('nil'), i.e. success.
     If key derivation fails, the state is updated
     by increasing the number of (attempted) address keys nonetheless,
     so that the next instance of this command will not re-try
     to derive the same key (which would fail again).
     If instead the command fails due to the index being @($2^{31}$),
     no state change happens.")
   (xdoc::p
    "Besides the updated state,
     we also return the address index of the key just derived,
     as well as the account address derived from the key.")
   (xdoc::p
    "The guard proofs of this operation need some of the constraints
     formalized in @(tsee stat-wfp).")
   (xdoc::p
    "This operation preserves
     the constraints formalized by @(tsee stat-wfp)."))
  (b* ((next-index (stat->addresses stat))
       ((when (= next-index (expt 2 31)))
        (mv (command-error-address-key-index-limit)
            next-index
            (repeat 20 0)
            (stat-fix stat)))
       (key-tree (stat->keys stat))
       ((mv error? new-key-tree)
        (bip32-extend-tree key-tree *key-path-prefix* next-index))
       ((when error?)
        (mv (command-error-address-key-derivation-fail next-index)
            next-index
            (repeat 20 0)
            (change-stat stat :addresses (1+ next-index))))
       (address (private-key-to-address
                 (bip32-get-priv-key-at-path
                  new-key-tree (rcons next-index *key-path-prefix*)))))
    (mv nil
        next-index
        address
        (change-stat stat :keys new-key-tree :addresses (1+ next-index))))
  :guard-hints (("Goal" :in-theory (enable stat-wfp
                                           stat-addresses-bounded-p
                                           stat-priv-keys-p
                                           stat-root-depth-zero-p
                                           stat-path-prefix-in-tree-p
                                           ubyte32p)))
  :no-function t
  ///

  (defrule stat-wfp-of-next-key
    (implies (and (statp stat)
                  (stat-wfp stat))
             (stat-wfp (mv-nth 3 (next-key stat))))
    :enable (stat-wfp
             stat-addresses-bounded-p
             stat-priv-keys-p
             stat-root-depth-zero-p
             stat-path-prefix-in-tree-p
             stat-all-valid-key-paths-p
             ubyte32-fix
             ubyte32p
             bip32-path-in-tree-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define save-stat ((stat statp) state)
  :guard (stat-wfp stat)
  :returns state
  :short "Save the state of the wallet to a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name suffix @('-stat') of this function
     is consistent with the type name @(tsee stat).
     It emphasizes the wallet state, as opposed to the ACL2 @(tsee state).")
   (xdoc::p
    "@(tsee serialize-write) throws a hard error upon failure.
     This may acceptable if the shell script that calls the wallet
     can catch that and turn into a more user-oriented error message."))
  (serialize-write *stat-filepath* stat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define load-stat (state)
  :returns (mv (error? maybe-command-error-p)
               (stat? maybe-statp)
               state)
  :short "Load the state of the wallet from a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name suffix @('-stat') of this function
     is consistent with the type name @(tsee stat).
     It emphasizes the wallet state, as opposed to the ACL2 @(tsee state).")
   (xdoc::p
    "@(tsee serialize-read) throws a hard error upon failure.
     This may acceptable if the shell script that calls the wallet
     can catch that and turn into a more user-oriented error message."))
  (b* (((mv stat? state) (serialize-read *stat-filepath*))
       ((unless (and (statp stat?) (stat-wfp stat?)))
        (mv (command-error-state-file-malformed) nil state)))
    (mv nil stat? state))
  :no-function t
  ///

  (defrule statp-of-load-stat-when-no-error
    (b* (((mv error? stat? &) (load-stat state)))
      (implies (not error?)
               (statp stat?))))

  (defrule stat-wfp-of-load-stat-when-no-error
    (b* (((mv error? stat? &) (load-stat state)))
      (implies (not error?)
               (stat-wfp stat?)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-stat-file-present (state)
  :returns (mv (error? maybe-command-error-p)
               state)
  :short "Ensure that the wallet state file exists."
  :long
  (xdoc::topstring
   (xdoc::p
    "Except for the initialization commands,
     the other wallet commands need
     to first read the wallet state from the file.
     Those commands call this function for that purpose.")
   (xdoc::p
    "This function returns @('nil') as first result if the file exists
     (i.e. no error);
     otherwise, it returns an error indicating the absence of the file.
     A different error is returned
     if the ACL2 function to test whether the file exists fails
     (that is, the file's existence cannot be tested);
     this should be a rare event.")
   (xdoc::p
    "If the file exists, we also check that it is a regular file."))
  (b* (((mv errmsg? file-existsp state) (path-exists-p *stat-filepath*))
       ((when errmsg?)
        (mv (command-error-state-file-untestable) state))
       ((unless file-existsp)
        (mv (command-error-state-file-absent) state))
       ((mv err kind state) (file-kind *stat-filepath* :follow-symlinks t))
       ((when (or err
                  (not (eq kind :regular-file))))
        (mv (command-error-state-file-not-regular) state)))
    (mv nil state))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-stat-file-absent (state)
  :returns (mv (error? maybe-command-error-p)
               state)
  :short "Ensure that the wallet state file does not already exist."
  :long
  (xdoc::topstring
   (xdoc::p
    "The initialization commands should not overwrite
     an existing wallet file.
     Thus, the initialization commands call this function
     to ensure that the file does not already exist.")
   (xdoc::p
    "This function is analogous to @(tsee check-stat-file-present),
     with the check ``flipped''."))
  (b* (((mv errmsg? file-existsp state) (path-exists-p *stat-filepath*))
       ((when errmsg?)
        (mv (command-error-state-file-untestable) state))
       ((when file-existsp)
        (mv (command-error-state-file-present) state)))
    (mv nil state))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mnemonic-message ((mnemonic stringp))
  :returns (msg msgp)
  :short "Build a message that describes a generated mnemonic."
  :long
  (xdoc::topstring
   (xdoc::p
    "When initializing a wallet from an entropy value,
     a mnemonic is generated,
     which is a non-empty string of words separated by individual spaces.
     This mnemonic must be shown to the user,
     as the result of running the command to initialize the wallet
     (from an entropy value).")
   (xdoc::p
    "This function builds a message that consists of
     the list of words, one per line, indented by two spaces."))
  (mnemonic-message-aux (strtok mnemonic (list #\Space)))
  :no-function t

  :prepwork
  ((define mnemonic-message-aux ((words string-listp))
     :returns (msg msgp)
     :parents nil
     (cond ((endp words) "")
           (t (msg "  ~s0~%~@1"
                   (car words)
                   (mnemonic-message-aux (cdr words)))))
     :no-function t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-init-from-entropy ((arguments string-listp) state)
  :returns (mv (msg msgp
                    :hints (("Goal" :in-theory (enable command-error-message))))
               state)
  :short "Process a command to initialize the wallet from an entropy value."
  :long
  (xdoc::topstring
   (xdoc::p
    "The message returned by this function describes an error if one occurs,
     otherwise it describes success and the generated mnemonic.")
   (xdoc::p
    "If no error occurs, the wallet state file is created."))
  (b* (((unless (= (len arguments) 2))
        (mv (command-error-message *command-name-init-from-entropy*
                                   (command-error-wrong-number-of-arguments
                                    2 (len arguments)))
            state))
       ((mv error? state) (check-stat-file-absent state))
       ((when error?)
        (mv (command-error-message *command-name-init-from-entropy* error?)
            state))
       (entropy-string (first arguments))
       (passphrase (second arguments))
       ((mv error? mnemonic stat?)
        (init-from-entropy entropy-string passphrase))
       ((when error?)
        (mv (command-error-message *command-name-init-from-entropy* error?)
            state))
       (msg (msg "The wallet has been successfully initialized ~
                  from the supplied entropy (and passphrase). ~
                  The generated mnemonic consists of the following words:~%~%~
                  ~@0~%~
                  Store this list of words in a safe place, ~
                  since it can be used to re-create this wallet. ~
                  Recall that, in order to do that, ~
                  these words must be passed to the initialization command ~
                  as a single string with single spaces separating them.~%~%"
                 (mnemonic-message mnemonic)))
       (state (save-stat stat? state)))
    (mv msg state))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-init-from-mnemonic ((arguments string-listp) state)
  :returns (mv (msg msgp
                    :hints (("Goal" :in-theory (enable command-error-message))))
               state)
  :short "Process a command to initialize the wallet from a mnenonic."
  :long
  (xdoc::topstring
   (xdoc::p
    "The message returned by this function describes an error if one occurs,
     otherwise it describes success.")
   (xdoc::p
    "If no error occurs, the wallet state file is created."))
  (b* (((unless (= (len arguments) 2))
        (mv (command-error-message *command-name-init-from-mnemonic*
                                   (command-error-wrong-number-of-arguments
                                    2 (len arguments)))
            state))
       ((mv error? state) (check-stat-file-absent state))
       ((when error?)
        (mv (command-error-message *command-name-init-from-mnemonic* error?)
            state))
       (mnemonic (first arguments))
       (passphrase (second arguments))
       ((mv error? stat?) (init-from-mnemonic mnemonic passphrase))
       ((when error?)
        (mv (command-error-message *command-name-init-from-mnemonic* error?)
            state))
       (state (save-stat stat? state))
       (msg (msg "The wallet has been successfully initialized ~
                  from the supplied mnemonic (and passphrase).~%~%")))
    (mv msg state))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transaction-message ((transaction byte-listp))
  :returns (msg msgp :hints (("Goal" :in-theory (enable transaction-message-line))))
  :short "Build a message that describes a (signed) transaction."
  :long
  (xdoc::topstring
   (xdoc::p
    "When signing a transaction, the signed transaction (a list of bytes)
     must be submitted to the Ethereum network.
     Since this wallet is meant to run on an air-gapped machine,
     the transaction must be copied to a connected machine for submission.
     Thus, the command to sign the transaction must show it on the screen.")
   (xdoc::p
    "This function builds a message that consists of all the bytes,
     each in hex form, separated by single spaces,
     16 bytes per line, each line indented by two spaces.
     In fact, this function handles any list of bytes,
     not just specifically signed transactions."))
  (cond ((endp transaction) "")
        ((< (len transaction) 16) (transaction-message-line transaction))
        (t (msg "~@0~@1"
                (transaction-message-line (take 16 transaction))
                (transaction-message (nthcdr 16 transaction)))))
  :no-function t

  :prepwork
  ((define transaction-message-line ((bytes byte-listp))
     :guard (consp bytes)
     :returns (msg msgp)
     :parents nil
     (msg " ~@0~%" (transaction-message-line-aux bytes))
     :no-function t

     :prepwork
     ((define transaction-message-line-aux ((bytes byte-listp))
        :returns (string stringp)
        :parents nil
        (cond ((endp bytes) "")
              (t (cat " "
                      (ubyte8s=>hexstring (list (car bytes)))
                      (transaction-message-line-aux (cdr bytes)))))
        :no-function t)))

   (local (include-book "std/lists/nthcdr" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-sign ((arguments string-listp) state)
  :returns (mv (msg msgp
                    :hints (("Goal" :in-theory (enable command-error-message))))
               state)
  :short "Process a transaction signing command."
  :long
  (xdoc::topstring
   (xdoc::p
    "The message returned by this function describes an error if one occurs,
     otherwise it describes success and the signed transaction.")
   (xdoc::p
    "The file is left unchanged,
     because this command does not change the state of the wallet."))
  (b* (((unless (= (len arguments) 7))
        (mv (command-error-message *command-name-sign*
                                   (command-error-wrong-number-of-arguments
                                    7 (len arguments)))
            state))
       ((mv error? state) (check-stat-file-present state))
       ((when error?)
        (mv (command-error-message *command-name-sign* error?)
            state))
       (nonce-string (first arguments))
       (gas-price-string (second arguments))
       (gas-limit-string (third arguments))
       (to-string (fourth arguments))
       (value-string (fifth arguments))
       (data-string (sixth arguments))
       (address-key-index-string (seventh arguments))
       ((mv error? stat? state) (load-stat state))
       ((when error?)
        (mv (command-error-message *command-name-sign* error?)
            state))
       ((mv error? signed-transaction) (sign nonce-string
                                             gas-price-string
                                             gas-limit-string
                                             to-string
                                             value-string
                                             data-string
                                             address-key-index-string
                                             stat?))
       ((when error?)
        (mv (command-error-message *command-name-sign* error?)
            state))
       (msg (msg "The transaction has been successfully signed ~
                  with the address key with index ~s0. ~
                  The signed transaction consists of the bytes~%~%~
                  ~@1~%"
                 address-key-index-string
                 (transaction-message signed-transaction))))
    (mv msg state))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-next-key ((arguments string-listp) state)
  :returns (mv (msg msgp
                    :hints (("Goal" :in-theory (enable command-error-message))))
               state)
  :short "Process a key generation command."
  :long
  (xdoc::topstring
   (xdoc::p
    "The message returned by this function describes an error if one occurs,
     otherwise it describes success along with
     the index and the address of the generated key.")
   (xdoc::p
    "The file is overwritten with the new wallet state."))
  (b* (((unless (= (len arguments) 0))
        (mv (command-error-message *command-name-next-key*
                                   (command-error-wrong-number-of-arguments
                                    2 (len arguments)))
            state))
       ((mv error? state) (check-stat-file-present state))
       ((when error?)
        (mv (command-error-message *command-name-next-key* error?)
            state))
       ((mv error? stat? state) (load-stat state))
       ((when error?)
        (mv (command-error-message *command-name-next-key* error?)
            state))
       ((mv error? index address stat) (next-key stat?))
       ((when error?)
        (mv (command-error-message *command-name-next-key* error?)
            state))
       (state (save-stat stat state))
       (msg (msg "The address key with index ~x0 ~
                  has been successfully generated. ~
                  Its associated 20-byte address is~%~%~
                  ~s1~s2~%"
                 index "  " (ubyte8s=>hexstring address))))
    (mv msg state))
  :guard-hints (("Goal"
                 :in-theory
                 (enable acl2::unsigned-byte-listp-rewrite-byte-listp)))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-command ((inputs string-listp) state)
  :returns (mv (msg msgp :hints (("Goal" :in-theory (disable msgp))))
               state)
  :short "Process a command."
  :long
  (xdoc::topstring
   (xdoc::p
    "The wallet is used via a command line interface
     provided by an OS shell script.
     The user types @('<script> <command> <argument1> ...'),
     where @('<script>') is the name of the shell script,
     @('<command>') is a wallet command (e.g. sign),
     and @('<argument1>') etc. are zero or more arguments for the command.
     The @('<command>'), @('argument1'), etc. arguments of the script
     are passed to this function as strings:
     thus, this function takes a list of strings as input.
     This function also takes the ACL2 state as input,
     necessary to manipulate the file that stores
     the persistent state of the wallet.")
   (xdoc::p
    "This function returns a message and a new ACL2 state.
     Implicit in the new ACL2 state is the creation or update
     of the file that stores the wallet state.
     The message is the user-oriented and user-visible outcome of the command.
     It may be an error message or a success message.")
   (xdoc::p
    "The shell script may be called with zero or more arguments.
     If it is called with zero arguments,
     there is no wallet command and it is an error.")
   (xdoc::p
    "Otherwise, we check whether the first argument
     is one of the wallet command,
     and if it is we process it accordingly;
     if it is not a valid command, it is an error.
     Each wallet command requires a certain number of inputs:
     these are all but the first arguments of the shell script."))
  (b* (((when (endp inputs))
        (mv (command-error-message "" (command-error-no-command))
            state))
       (command (car inputs))
       (arguments (cdr inputs))
       ((when (equal command *command-name-init-from-entropy*))
        (process-init-from-entropy arguments state))
       ((when (equal command *command-name-init-from-mnemonic*))
        (process-init-from-mnemonic arguments state))
       ((when (equal command *command-name-sign*))
        (process-sign arguments state))
       ((when (equal command *command-name-next-key*))
        (process-next-key arguments state)))
    (mv (command-error-message command (command-error-wrong-command command))
        state))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection wallet
  :short "Entry point to the ACL2 code of the wallet."
  :long
  (xdoc::topstring
   (xdoc::p
    "For the main documentation topic, please go "
    (xdoc::seetopic "crypto-hdwallet" "up one level to CRYPTO-HDWALLET")
    ".")
   (xdoc::p
    "This is a macro, with an associated function as is customary.
     The function processes the inputs from the shell script
     and displays the resulting message.
     The macro wraps the function call in a @(tsee make-event)
     that keeps the output ``clean''
     and that automatically passes the ACL2 state to the function.
     The macro is called with the strings from the shell script as arguments.")
   (xdoc::@def "wallet"))

  (define wallet-fn ((inputs string-listp) state)
    :returns (mv erp val state)
    :parents nil
    (b* (((mv msg state) (process-command inputs state))
         (- (cw "~%~@0~%" msg)))
      (value '(value-triple :invisible)))
    :no-function t)

  (defmacro wallet (&rest inputs)
    `(with-output :off :all :on error
       (make-event
        (wallet-fn (list ,@inputs) state)
        :on-behalf-of :quiet))))
