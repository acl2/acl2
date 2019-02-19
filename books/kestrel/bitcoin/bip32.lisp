; Bitcoin -- Bitcoin Improvement Proposal (BIP) 32
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "kestrel/utilities/fixbytes/ubyte32-list" :dir :system)

(include-book "crypto")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bip32
  :parents (bitcoin)
  :short "Bitcoin Improvement Proposal (BIP) 32."
  :long
  (xdoc::topapp
   (xdoc::p
    "This is described at
     <a href=\"https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki\"
     >this page in the @('bitcoin/bips') repository on GitHub</a>,
     linked from
     <a href=\"https://en.bitcoin.it/wiki/BIP_0032\"
     >Page `BIP 0032' of [Wiki]</a>.
     We refer to the document at the first URL as `[BIP32]'
     in the documentation below."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc bip32-conventions
  :short "BIP 32 conventions."
  :long
  (xdoc::topapp
   (xdoc::p
    "As stated in the 'Conventions' section of [BIP32],
     the elliptic curve cryptography is based on the secp256k1 curve.
     In our model, the types for private and public keys are
     @(tsee secp256k1-priv-key-p) and @(tsee secp256k1-pub-key-p).")
   (xdoc::p
    "The conversion functions described in the 'Conventions' section of [BIP32]
     are formalized as follows in our model:")
   (xdoc::ul
    (xdoc::li
     "@($\\mathsf{point}$) is @(tsee secp256k1-mul)
      with point @(tsee secp256k1-generator);
      when the argument is a private key,
      we use @(tsee secp256k1-priv-to-pub).")
    (xdoc::li
     "@($\\mathsf{ser}_{32}$) is @(tsee nat=>bendian)
      with base 256 and width 4.")
    (xdoc::li
     "@($\\mathsf{ser}_{256}$) is @(tsee nat=>bendian)
      with base 256 and width 32.")
    (xdoc::li
     "@($\\mathsf{ser}_\\mathsf{P}$) is @(tsee secp256k1-point-to-bytes)
      with the compression flag set.")
    (xdoc::li
     "@($\\mathsf{parse}_{256}$) is @(tsee bendian=>nat) with base 256."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-chain-code
  :short "Fixtype of chain codes."
  :long
  (xdoc::topp
   "A chain code consists of 32 bytes.
    Chain codes are used in both extended private and public keys.")

  (define bip32-chain-code-p (x)
    :returns (yes/no booleanp)
    :parents (bip32-chain-code)
    :short "Recognizer for @(tsee bip32-chain-code)."
    (and (byte-listp x)
         (equal (len x) 32))
    :no-function t
    ///

    (defrule byte-listp-when-bip32-chain-code-p
      (implies (bip32-chain-code-p cc)
               (byte-listp cc))
      :rule-classes :tau-system)

    (defrule len-when-bip32-chain-code-p
      (implies (bip32-chain-code-p x)
               (equal (len x) 32))
      :rule-classes :tau-system))

  (define bip32-chain-code-fix ((x bip32-chain-code-p))
    :returns (fixed-x bip32-chain-code-p)
    :parents (bip32-chain-code)
    :short "Fixer for @(tsee bip32-chain-code)."
    (mbe :logic (if (bip32-chain-code-p x) x (repeat 32 0))
         :exec x)
    :no-function t
    ///
    (defrule bip32-chain-code-fix-when-bip32-chain-code-p
      (implies (bip32-chain-code-p x)
               (equal (bip32-chain-code-fix x)
                      x))))

  (fty::deffixtype bip32-chain-code
    :pred bip32-chain-code-p
    :fix bip32-chain-code-fix
    :equiv bip32-chain-code-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bip32-ext-priv-key
  :short "Fixtype of extended private keys."
  :long
  "<p>
   An extended private key consists of a private key and a chain code.
   </p>"
  ((key secp256k1-priv-key)
   (chain-code bip32-chain-code))
  :layout :list
  ///

  (defrule posp-of-bip32-ext-priv-key->key
    (posp (bip32-ext-priv-key->key extprivkey))
    :rule-classes :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bip32-ext-pub-key
  :short "Fixtype of extended public keys."
  :long
  "<p>
   An extended public key consists of a public key and a chain code.
   </p>"
  ((key secp256k1-pub-key)
   (chain-code bip32-chain-code))
  :layout :list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-ckd-priv ((parent bip32-ext-priv-key-p) (i ubyte32p))
  :returns (mv (error? booleanp)
               (child bip32-ext-priv-key-p))
  :short "Private child key derivation."
  :long
  (xdoc::topapp
   (xdoc::p
    "This is the function @($\\mathsf{CKDpriv}$) in [BIP32].")
   (xdoc::p
    "The first result is @('t') when the key cannot be computed,
     as specified in [BIP32];
     in this case, the second result is irrelevant
     (and we just return the parent key).
     Otherwise, the first result is @('nil'), meaning no error."))
  (b* (((bip32-ext-priv-key parent) parent)
       (irrelevant-child (bip32-ext-priv-key-fix parent))
       (i (mbe :logic (ubyte32-fix i) :exec i))
       (data (if (>= i (expt 2 31))
                 (append (list 0)
                         (nat=>bendian 256 32 parent.key)
                         (nat=>bendian 256 4 i))
               (append (secp256k1-point-to-bytes
                        (secp256k1-priv-to-pub parent.key)
                        t)
                       (nat=>bendian 256 4 i))))
       (big-i (hmac-sha-512 parent.chain-code data))
       (big-i-l (take 32 big-i))
       (big-i-r (nthcdr 32 big-i))
       (parsed-big-i-l (bendian=>nat 256 big-i-l))
       (n (secp256k1-order))
       ((when (>= parsed-big-i-l n)) (mv t irrelevant-child))
       (child.key (mod (+ parsed-big-i-l parent.key) n))
       ((when (= child.key 0)) (mv t irrelevant-child))
       (child.chain-code big-i-r))
    (mv nil (bip32-ext-priv-key child.key child.chain-code)))
  :no-function t
  :guard-hints (("Goal"
                 :in-theory (e/d (ubyte32p
                                  dab-digit-listp-of-256-rewrite-byte-listp
                                  bip32-chain-code-p
                                  secp256k1-priv-key-p)
                                 (mod))))
  :prepwork ((local (include-book "std/lists/nthcdr" :dir :system))
             (local (include-book "arithmetic-5/top" :dir :system)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-ckd-pub ((parent bip32-ext-pub-key-p) (i ubyte32p))
  :returns (mv (error? booleanp)
               (child bip32-ext-pub-key-p))
  :short "Public child key derivation from public parent key."
  :long
  (xdoc::topapp
   (xdoc::p
    "This is the function @($\\mathsf{CKDpub}$) in [BIP32].")
   (xdoc::p
    "The first result is @('t')
     if the index is @($2^{31}$) or more
     or if the key cannot be computed,
     as specified in [BIP32];
     in these cases, the second result is irrelevant
     (and we just return the parent key).
     Otherwise, the first result is @('nil'), meaning no error.")
   (xdoc::p
    "We could have restricted the argument @('i') to be below @($2^{31}$),
     but [BIP32] handles the error explicitly in the definition of the function,
     so we do the same here."))
  (b* (((bip32-ext-pub-key parent) parent)
       (irrelevant-child (bip32-ext-pub-key-fix parent))
       (i (mbe :logic (ubyte32-fix i) :exec i))
       ((when (>= i (expt 2 31))) (mv t irrelevant-child))
       (data (append (secp256k1-point-to-bytes parent.key t)
                     (nat=>bendian 256 4 i)))
       (big-i (hmac-sha-512 parent.chain-code data))
       (big-i-l (take 32 big-i))
       (big-i-r (nthcdr 32 big-i))
       (parsed-big-i-l (bendian=>nat 256 big-i-l))
       (n (secp256k1-order))
       ((when (>= parsed-big-i-l n)) (mv t irrelevant-child))
       (child.key (secp256k1-add (secp256k1-mul parsed-big-i-l
                                                (secp256k1-generator))
                                 parent.key))
       ((when (secp256k1-infinityp child.key)) (mv t irrelevant-child))
       (child.chain-code big-i-r))
    (mv nil (bip32-ext-pub-key child.key child.chain-code)))
  :no-function t
  :guard-hints (("Goal"
                 :in-theory (enable secp256k1-pub-key-p
                                    bip32-chain-code-p
                                    dab-digit-listp-of-256-rewrite-byte-listp)))
  :prepwork ((local (include-book "std/lists/nthcdr" :dir :system)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-n ((private bip32-ext-priv-key-p))
  :returns (extpubkey bip32-ext-pub-key-p)
  :short "Calculate an extended public key from an extended private key."
  :long
  (xdoc::topapp
   (xdoc::p
    "This is the function @($\\mathsf{N}$) in [BIP32]."))
  (b* (((bip32-ext-priv-key private) private)
       (public.key (secp256k1-priv-to-pub private.key))
       (public.chain-code private.chain-code))
    (bip32-ext-pub-key public.key public.chain-code))
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-ckd-priv-pub ((parent bip32-ext-priv-key-p) (i ubyte32p))
  :returns (mv (error? booleanp)
               (child bip32-ext-pub-key-p))
  :short "Public child key derivation from private parent key,
          for both hardened and non-hardened child keys."
  :long
  (xdoc::topapp
   (xdoc::p
    "There is no explicitly named function for this in [BIP32],
     but this corresponds to the expression
     @($\\mathsf{N}
        (\\mathsf{CKDpriv}
         ((\\mathsf{k}_\\mathsf{par},\\mathsf{c}_\\mathsf{par}),
          \\mathsf{i}))$)
     in [BIP32].
     We define an explicit function for that here.")
   (xdoc::p
    "In case of error, we return an irrelevant child key."))
  (b* ((irrelevant-child (bip32-n parent))
       ((mv error? child-priv) (bip32-ckd-priv parent i))
       ((when error?) (mv t irrelevant-child))
       (child-pub (bip32-n child-priv)))
    (mv nil child-pub))
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-ckd-priv-pub-nh ((parent bip32-ext-priv-key-p) (i ubyte32p))
  :returns (mv (error? booleanp)
               (child bip32-ext-pub-key-p))
  :short "Public child key derivation from private parent key,
          for non-hardedned child keys only."
  :long
  (xdoc::topapp
   (xdoc::p
    "There is no explicitly named function for this in [BIP32],
     but this corresponds to the expression
     @($\\mathsf{CKDpub}
        (\\mathsf{N}
         (\\mathsf{k}_\\mathsf{par},\\mathsf{c}_\\mathsf{par}),
         \\mathsf{i})$)
     in [BIP32].
     We define an explicit function for that here.")
   (xdoc::p
    "In case of error, we return an irrelevant child key.")
   (xdoc::p
    "Proving the equivalence of this function with @(tsee bip32-ckd-priv-pub)
     (for non-hardened child keys)
     requires the use of certain properties of elliptic curve operations
     that are currently not formalized in the secp256k1 placeholder.
     Thus, this proof will be done later."))
  (bip32-ckd-pub (bip32-n parent) i)
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc bip32-path
  :short "Paths in a tree of keys."
  :long
  (xdoc::topapp
   (xdoc::p
    "Each key in a tree is designated by
     a list of zero or more unsigned 32-bit bytes,
     each of which is a key index @('i')
     as used in the child key derivation functions.
     The empty path designates the root of the tree.")
   (xdoc::p
    "This kind of path corresponds to the notation
     @($\\mathsf{a/b/c}$) used in [BIP32].
     However, we do not use any explicit @($\\mathsf{H}$) subscripts
     to denote indices of hardened keys;
     we simply use indices whose most significant bit is set,
     e.g. @($3_\\mathsf{H}$) is index @($2^{31}+3$).")
   (xdoc::p
    "The functions @(tsee bip32-ckd-priv*) and @(tsee bip32-ckd-pub*)
     lift @(tsee bip32-ckd-priv) and @(tsee bip32-ckd-pub)
     from single indices to paths.
     These key derivation functions on paths designate keys in a tree,
     starting with a root.
     All the derivations in the path must be valid (i.e. return no error)
     in order for a path to designate a valid key;
     otherwise, as stated in [BIP32], the corresponding key is skipped.")
   (xdoc::p
    "In our formalization of BIP 32,
     we use the library fixtype @(tsee ubyte32-list) for paths.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-ckd-priv* ((root bip32-ext-priv-key-p) (path ubyte32-listp))
  :returns (mv (error? booleanp)
               (key bip32-ext-priv-key-p))
  :short "Private key designated by
          a specified path in the tree with the specified root private key."
  (b* ((root (mbe :logic (bip32-ext-priv-key-fix root) :exec root))
       ((when (endp path)) (mv nil root))
       ((mv error? next) (bip32-ckd-priv root (car path)))
       ((when error?) (mv t root)))
    (bip32-ckd-priv* next (cdr path)))
  :no-function t
  :measure (len path)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-ckd-pub* ((root bip32-ext-pub-key-p) (path ubyte32-listp))
  :returns (mv (error? booleanp)
               (key bip32-ext-pub-key-p))
  :short "Public key designated by
          a specified path in the tree with the specified root public key."
  (b* ((root (mbe :logic (bip32-ext-pub-key-fix root) :exec root))
       ((when (endp path)) (mv nil root))
       ((mv error? next) (bip32-ckd-pub root (car path)))
       ((when error?) (mv t root)))
    (bip32-ckd-pub* next (cdr path)))
  :no-function t
  :measure (len path)
  :hooks (:fix))
