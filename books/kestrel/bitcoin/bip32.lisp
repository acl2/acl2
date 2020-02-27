; Bitcoin Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "kestrel/crypto/interfaces/hmac-sha-512" :dir :system)
(include-book "kestrel/crypto/ecurve/secp256k1-interface" :dir :system)
(include-book "kestrel/fty/defbytelist-standard-instances" :dir :system)
(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "kestrel/fty/defset" :dir :system)
(include-book "kestrel/std/util/deffixer" :dir :system)
(include-book "kestrel/utilities/define-sk" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

(include-book "bytes")
(include-book "crypto")

(local (include-book "kestrel/utilities/lists/prefixp-theorems" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/prefixp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bip32
  :parents (bitcoin)
  :short "Bitcoin Improvement Proposal (BIP) 32."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is described at
     <a href=\"https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki\"
     >this page in the @('bitcoin/bips') repository on GitHub</a>,
     linked from
     <a href=\"https://en.bitcoin.it/wiki/BIP_0032\"
     >Page `BIP 0032' of [Wiki]</a>.
     We refer to the document at the first URL as `[BIP32]'
     in the documentation below.")
   (xdoc::p
    "As stated in the 'Conventions' section of [BIP32],
     the elliptic curve cryptography is based on the secp256k1 curve.
     In our model, the types for private and public keys are
     @(tsee secp256k1-priv-key-p) and @(tsee secp256k1-pub-key-p).")
   (xdoc::p
    "The conversion functions described in the 'Conventions' section of [BIP32]
     are formalized as follows in our model of Bitcoin:")
   (xdoc::ul
    (xdoc::li
     "@($\\mathsf{point}$) is @(tsee secp256k1-mul)
      with point @(tsee secp256k1-point-generator);
      when the argument is a private key,
      we use @(tsee secp256k1-priv-to-pub).")
    (xdoc::li
     "@($\\mathsf{ser}_{32}$) is @(tsee nat=>bebytes) with width 4.")
    (xdoc::li
     "@($\\mathsf{ser}_{256}$) is @(tsee nat=>bebytes) with width 32.")
    (xdoc::li
     "@($\\mathsf{ser}_\\mathsf{P}$) is @(tsee secp256k1-point-to-bytes)
      with the compression flag set.")
    (xdoc::li
     "@($\\mathsf{parse}_{256}$) is @(tsee bebytes=>nat)."))
   (xdoc::p
    "The operations defined below should suffice to cover
     the use cases that BIP 32 should cater to:")
   (xdoc::ul
    (xdoc::li
     "Given a seed, @(tsee bip32-master-tree) is used to generate
      a singleton tree with the master private key at the root.")
    (xdoc::li
     "This master tree is extended as needed,
      via @(tsee bip32-extend-tree).")
    (xdoc::li
     "For signing, private keys can be retrieved from the tree
      via @(tsee bip32-get-priv-key-at-path).
      For calculating addresses, auditing, etc.,
      public keys can be retrieved from the tree
      via @(tsee bip32-get-pub-key-at-path).")
    (xdoc::li
     "For sharing (subtrees of) the master tree,
      @(tsee bip32-export-key) is used to serialize a (private or public) key.
      Then @(tsee bip32-import-key) is used to
      construct a separate (sub)tree rooted at that key.")
    (xdoc::li
     "(Sub)trees shared as just explained can be then operated upon via
      @(tsee bip32-extend-tree) for deriving more keys,
      @(tsee bip32-get-priv-key-at-path) for signing
      (unless the tree consists of public keys),
      @(tsee bip32-get-pub-key-at-path) for
      calculating addresses, auditing, etc.,
      and @(tsee bip32-export-key) for further sharing.")))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bip32-extended-keys
  :parents (bip32)
  :short "Extended keys."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-chain-code
  :short "Chain codes."
  :long
  (xdoc::topstring-p
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
               (byte-listp cc)))

    (defrule len-when-bip32-chain-code-p
      (implies (bip32-chain-code-p x)
               (equal (len x) 32))
      :rule-classes :tau-system))

  (std::deffixer bip32-chain-code-fix
    :pred bip32-chain-code-p
    :body-fix (repeat 32 0)
    :parents (bip32-chain-code)
    :short "Fixer for @(tsee bip32-chain-code).")

  (fty::deffixtype bip32-chain-code
    :pred bip32-chain-code-p
    :fix bip32-chain-code-fix
    :equiv bip32-chain-code-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bip32-ext-priv-key
  :short "Extended private keys."
  :long
  (xdoc::topstring-p
   "An extended private key consists of a private key and a chain code.")
  ((key secp256k1-priv-key)
   (chain-code bip32-chain-code))
  :layout :list
  ///

  (defrule posp-of-bip32-ext-priv-key->key
    (posp (bip32-ext-priv-key->key extprivkey))
    :rule-classes :type-prescription)

  (defrule len-of-bip32-ext-priv-key->chain-code
    (equal (len (bip32-ext-priv-key->chain-code key))
           32)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bip32-ext-pub-key
  :short "Extended public keys."
  :long
  (xdoc::topstring-p
   "An extended public key consists of a public key and a chain code.")
  ((key secp256k1-pub-key)
   (chain-code bip32-chain-code))
  :layout :list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum bip32-ext-key
  :short "Extended keys (private or public)."
  :long
  (xdoc::topstring-p
   "This is the (disjoint) union of extended private and public keys.")
  (:priv ((get bip32-ext-priv-key)))
  (:pub ((get bip32-ext-pub-key)))
  ///

  (defrule len-of-bip32-ext-pub-key->chain-code
    (equal (len (bip32-ext-pub-key->chain-code key))
           32)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bip32-key-derivation
  :parents (bip32)
  :short "Key derivation functions."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-ckd-priv ((parent bip32-ext-priv-key-p) (i ubyte32p))
  :returns (mv (error? booleanp)
               (child bip32-ext-priv-key-p))
  :short "Private child key derivation."
  :long
  (xdoc::topstring
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
                         (nat=>bebytes 32 parent.key)
                         (nat=>bebytes 4 i))
               (append (secp256k1-point-to-bytes
                        (secp256k1-priv-to-pub parent.key)
                        t)
                       (nat=>bebytes 4 i))))
       (big-i (hmac-sha-512 parent.chain-code data))
       (big-i-l (take 32 big-i))
       (big-i-r (nthcdr 32 big-i))
       (parsed-big-i-l (bebytes=>nat big-i-l))
       (n (secp256k1-order))
       ((when (>= parsed-big-i-l n)) (mv t irrelevant-child))
       (child.key (mod (+ parsed-big-i-l parent.key) n))
       ((when (= child.key 0)) (mv t irrelevant-child))
       (child.chain-code big-i-r))
    (mv nil (bip32-ext-priv-key child.key child.chain-code)))
  :no-function t
  :guard-hints (("Goal"
                 :in-theory (e/d (ubyte32p
                                  bip32-chain-code-p
                                  secp256k1-priv-key-p
                                  secp256k1-order)
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
  (xdoc::topstring
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
                     (nat=>bebytes 4 i)))
       (big-i (hmac-sha-512 parent.chain-code data))
       (big-i-l (take 32 big-i))
       (big-i-r (nthcdr 32 big-i))
       (parsed-big-i-l (bebytes=>nat big-i-l))
       (n (secp256k1-order))
       ((when (>= parsed-big-i-l n)) (mv t irrelevant-child))
       (child.key (secp256k1-add (secp256k1-mul parsed-big-i-l
                                                (secp256k1-point-generator))
                                 parent.key))
       ((when (secp256k1-point-infinityp child.key)) (mv t irrelevant-child))
       (child.chain-code big-i-r))
    (mv nil (bip32-ext-pub-key child.key child.chain-code)))
  :no-function t
  :guard-hints (("Goal"
                 :in-theory (enable secp256k1-pub-key-p
                                    bip32-chain-code-p)))
  :prepwork ((local (include-book "std/lists/nthcdr" :dir :system)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-ckd ((parent bip32-ext-key-p) (i ubyte32p))
  :returns (mv (error? booleanp)
               (child bip32-ext-key-p))
  :short "Child key derivation from parent key."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the sum of @(tsee bip32-ckd-priv) and @(tsee bip32-ckd-pub).
     It maps (extended) parent private keys to (extended) child private keys
     and (extended) parent public keys to (extended) child public keys.
     This function does not appear in [BIP32]."))
  (bip32-ext-key-case
   parent
   :priv (b* (((mv error? child) (bip32-ckd-priv parent.get i)))
           (mv error? (bip32-ext-key-priv child)))
   :pub (b* (((mv error? child) (bip32-ckd-pub parent.get i)))
          (mv error? (bip32-ext-key-pub child))))
  :no-function t
  :hooks (:fix)
  ///

  (defrule bip32-ext-key-kind-of-bip32-ckd
    (equal (bip32-ext-key-kind (mv-nth 1 (bip32-ckd parent i)))
           (bip32-ext-key-kind parent))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-n ((private bip32-ext-priv-key-p))
  :returns (extpubkey bip32-ext-pub-key-p)
  :short "Calculate an extended public key from an extended private key."
  :long
  (xdoc::topstring
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
  (xdoc::topstring
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
  (xdoc::topstring
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
     that are currently not formalized in the secp256k1 interface.
     Thus, this proof will be done later."))
  (bip32-ckd-pub (bip32-n parent) i)
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bip32-key-trees
  :parents (bip32)
  :short "Key trees."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc bip32-path
  :short "Paths in key trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in [BIP32],
     the derivation of child keys from parent keys give rise to key trees.
     Each key in a tree is designated by
     a list of zero or more unsigned 32-bit bytes,
     each of which is a key index @('i')
     as used in the child key derivation functions;
     the empty path designates the root of the tree.")
   (xdoc::p
    "This kind of path corresponds to the notation
     @($\\mathsf{a/b/c}$) used in [BIP32].
     However, we do not use any explicit @($\\mathsf{H}$) subscripts
     to denote indices of hardened keys;
     we simply use indices whose most significant bit is set,
     e.g. @($3_\\mathsf{H}$) is index @($2^{31}+3$).")
   (xdoc::p
    "Below we lift the key derivation functions from single indices to paths.
     These key derivation functions on paths designate keys in a tree,
     starting with a root.
     All the derivations in the path must be valid (i.e. return no error)
     in order for a path to designate a valid key;
     otherwise, as stated in [BIP32], the corresponding key is skipped.")
   (xdoc::p
    "In our formalization of BIP 32,
     we use the library type @(tsee ubyte32-list) for paths.")))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-ckd* ((root bip32-ext-key-p) (path ubyte32-listp))
  :returns (mv (error? booleanp)
               (key bip32-ext-key-p))
  :short "Key designated by
          a specified path in the tree with the specified root key."
  (bip32-ext-key-case
   root
   :priv (b* (((mv error? key) (bip32-ckd-priv* root.get path)))
           (mv error? (bip32-ext-key-priv key)))
   :pub (b* (((mv error? key) (bip32-ckd-pub* root.get path)))
          (mv error? (bip32-ext-key-pub key))))
  :no-function t
  :hooks (:fix)
  ///

  (defrule bip32-ext-key-kind-of-bip32-ckd*
    (equal (bip32-ext-key-kind (mv-nth 1 (bip32-ckd* root path)))
           (bip32-ext-key-kind root))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset bip32-path-set
  :elt-type ubyte32-list
  :elementp-of-nil t
  :pred bip32-path-setp
  :fix bip32-path-sfix
  :short "Osets of paths in key trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "At any point in time, a system (e.g. wallet) contains
     a relatively small subset
     of the complete tree of possible keys derived from a root.
     We represent the current tree as a finite set of paths
     that satisfies additional conditions explicated later.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-path-set-closedp
  :short "Check if a set of key tree paths is closed under prefix."
  :long
  (xdoc::topstring
   (xdoc::p
    "The set of paths of a tree is closed under prefix:
     if a path is in the tree, every prefix path is in the tree too.
     Thus, in order to represent a tree (of keys),
     a set of paths must satisfy this condition.")
   (xdoc::p
    "The condition that the prefix is a true list
     is needed because @(tsee prefixp) ignores the final @(tsee cdr)s.
     Without this condition, prefixes that are not true lists
     would be required to be in the set,
     which would be impossible because the set's elements are all true lists.")
   (xdoc::p
    "We introduce this function as a constrained function,
     so that we can make an executable attachment for it
     (in @('bip32-executable.lisp')).
     Since currently @(tsee std::define-sk) does not support
     @(tsee defun-sk)'s @(':constrain') and
     @(tsee defun-sk) forces the guard to @('t') when @(':constrain') is @('t'),
     we use an @(tsee encapsulate) for now to introduce this function.
     A @(tsee std::define-sk) is used to locally define the witness,
     which also guard-verifies the matrix of the function,
     as additional validation.")
   (xdoc::p
    "A closed non-empty set of paths always contains the empty path,
     because the empty path is a prefix of every path.")
   (xdoc::p
    "The singleton set consisting of the empty path is closed.")
   (xdoc::p
    "If a set of paths is closed under prefix,
     extending a path in the set
     (more precisely, extending the set with the path obtained by
     extending an existing path in the set)
     results in a set of paths that is still closed under prefix.
     This is because every strict prefix of the new path
     is also a prefix of the existing path,
     and therefore already in the set by hypothesis."))

  (encapsulate
    (((bip32-path-set-closedp *) => *
      :formals (paths)
      :guard (bip32-path-setp paths))
     ((bip32-path-set-closedp-witness *) => (mv * *)))

    (local
     (define-sk bip32-path-set-closedp ((paths bip32-path-setp))
       :returns (yes/no booleanp :name bip32-path-set-closedp-return-type)
       (forall (path prefix)
               (b* ((paths (bip32-path-sfix paths)))
                 (implies (and (in path paths)
                               (true-listp prefix)
                               (prefixp prefix path))
                          (in prefix paths))))
       ///
       (fty::deffixequiv-sk bip32-path-set-closedp
         :args ((paths bip32-path-setp)))))

    (defruled bip32-path-set-closedp-definition
      (equal (bip32-path-set-closedp paths)
             (mv-let (path prefix)
               (bip32-path-set-closedp-witness paths)
               (b* ((paths (bip32-path-sfix paths)))
                 (implies (and (in path paths)
                               (true-listp prefix)
                               (prefixp prefix path))
                          (in prefix paths)))))
      :rule-classes :definition
      :enable bip32-path-set-closedp)

    (defrule booleanp-of-bip32-path-set-closedp
      (booleanp (bip32-path-set-closedp paths))
      :rule-classes (:rewrite :type-prescription))

    (defruled bip32-path-set-closedp-necc
      (implies (bip32-path-set-closedp paths)
               (b* ((paths (bip32-path-sfix paths)))
                 (implies (and (in path paths)
                               (true-listp prefix)
                               (prefixp prefix path))
                          (in prefix paths))))
      :enable bip32-path-set-closedp-necc)

    (fty::deffixequiv bip32-path-set-closedp
      :args ((paths bip32-path-setp))))

  (defrule empty-path-in-closed-nonempty-bip32-path-set
    (implies (and (bip32-path-setp paths)
                  (not (empty paths))
                  (bip32-path-set-closedp paths))
             (in nil paths))
    :use (:instance bip32-path-set-closedp-necc
          (prefix nil)
          (path (head paths))))

  (defrule bip32-path-set-closedp-of-singleton-empty-path
    (bip32-path-set-closedp '(nil))
    :enable (in bip32-path-set-closedp-definition))

  (defrule bip32-path-set-closedp-of-insert-of-rcons
    (implies (and (bip32-path-setp paths)
                  (bip32-path-set-closedp paths)
                  (in path paths)
                  (ubyte32p index))
             (bip32-path-set-closedp (insert (rcons index path) paths)))
    :enable (list-equiv bip32-path-set-closedp-definition)
    :use ((:instance bip32-path-set-closedp-necc
           (path (mv-nth 0 (bip32-path-set-closedp-witness
                            (insert (rcons index path) paths))))
           (prefix (mv-nth 1 (bip32-path-set-closedp-witness
                              (insert (rcons index path) paths)))))
          (:instance bip32-path-set-closedp-necc
           (prefix (mv-nth 1 (bip32-path-set-closedp-witness
                              (insert (rcons index path) paths))))))
    :cases ((equal (mv-nth 1 (bip32-path-set-closedp-witness
                              (insert (rcons index path) paths)))
                   (mv-nth 0 (bip32-path-set-closedp-witness
                              (insert (rcons index path) paths)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-index-tree
  :short "Index trees underlying key trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "As defined later, a key tree includes a tree of indices,
     represented as a closed non-empty set of paths.")
   (xdoc::p
    "Extending a path of an index tree results in a index tree,
     because the extension preserves
     non-emptiness and prefix closure."))

  (define bip32-index-treep (x)
    :returns (yes/no booleanp)
    :parents (bip32-index-tree)
    :short "Recognizer for @(tsee bip32-index-tree)."
    (and (bip32-path-setp x)
         (not (empty x))
         (bip32-path-set-closedp x))
    :no-function t
    ///

    (defrule bip32-path-setp-when-bip32-index-treep
      (implies (bip32-index-treep x)
               (bip32-path-setp x))
      :rule-classes (:rewrite :forward-chaining))

    (defrule bip32-index-treep-of-singleton-empty-path
      (bip32-index-treep '(nil))
      :disable ((bip32-index-treep)))

    (in-theory (disable (:e bip32-index-treep))))

  (std::deffixer bip32-index-tree-fix
    :pred bip32-index-treep
    :body-fix (list nil)
    :parents (bip32-index-tree)
    :short "Fixer for @(tsee bip32-index-tree).")

  (in-theory (disable (:e bip32-index-tree-fix)))

  (fty::deffixtype bip32-index-tree
    :pred bip32-index-treep
    :fix bip32-index-tree-fix
    :equiv bip32-index-tree-equiv
    :define t
    :forward t)

  (defrule bip32-index-treep-of-insert-of-rcons
    (implies (and (bip32-index-treep paths)
                  (in path paths)
                  (ubyte32p index))
             (bip32-index-treep (insert (rcons index path) paths)))
    :enable bip32-index-treep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-valid-keys-p
  :short "Check if all the derived keys in a (tree's) set of paths are valid."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a root key, every path in a tree must correspond to a valid key.
     That is, all the key derivations along the path must be valid.")
   (xdoc::p
    "This function checks this condition.
     This function is used to define key trees later.")
   (xdoc::p
    "Even though this function is applied to index trees,
     it can be defined on general sets of paths.")
   (xdoc::p
    "We introduce this function as a constrained function,
     so that we can make an executable attachment for it
     (in @('bip32-executable.lisp')).
     Since currently @(tsee std::define-sk) does not support
     @(tsee defun-sk)'s @(':constrain') and
     @(tsee defun-sk) forces the guard to @('t') when @(':constrain') is @('t'),
     we use an @(tsee encapsulate) for now to introduce this function.
     A @(tsee std::define-sk) is used to locally define the witness,
     which also guard-verifies the matrix of the function,
     as additional validation.")
   (xdoc::p
    "The singleton tree consisting of just the root
     (represented as the singleton set consisting of the empty path)
     trivially satisfies this key validity condition.")
   (xdoc::p
    "Extending a path of an index tree
     preserves the validity of the keys,
     provided that the key at the end of the new extended path is valid.")
   (xdoc::p
    "The tail of a set of paths with valid keys also has all valid keys."))

  (encapsulate
    (((bip32-valid-keys-p * *) => *
      :formals (root paths)
      :guard (and (bip32-ext-key-p root) (bip32-path-setp paths)))
     ((bip32-valid-keys-p-witness * *) => *))

    (local
     (define-sk bip32-valid-keys-p ((root bip32-ext-key-p)
                                    (paths bip32-path-setp))
       :returns (yes/no booleanp :name bip32-valid-keys-p-return-type)
       (forall (path)
               (implies (in path (bip32-path-sfix paths))
                        (not (mv-nth 0 (bip32-ckd* root path)))))
       ///
       (fty::deffixequiv-sk bip32-valid-keys-p
         :args ((root bip32-ext-key-p) (paths bip32-path-setp)))))

    (defruled bip32-valid-keys-p-definition
      (equal (bip32-valid-keys-p root paths)
             (let ((path (bip32-valid-keys-p-witness root paths)))
               (implies (in path (bip32-path-sfix paths))
                        (not (mv-nth 0 (bip32-ckd* root path))))))
      :rule-classes :definition
      :enable bip32-valid-keys-p)

    (defrule booleanp-of-bip32-valid-keys-p
      (booleanp (bip32-valid-keys-p root paths))
      :rule-classes (:rewrite :type-prescription))

    (defruled bip32-valid-keys-p-necc
      (implies (bip32-valid-keys-p root paths)
               (implies (in path (bip32-path-sfix paths))
                        (not (mv-nth 0 (bip32-ckd* root path)))))
      :enable bip32-valid-keys-p-necc)

    (fty::deffixequiv bip32-valid-keys-p
      :args ((root bip32-ext-key-p) (paths bip32-path-setp))))

  (defrule bip32-valid-keys-p-of-singleton-empty-path
    (bip32-valid-keys-p root '(nil))
    :enable (in
             bip32-valid-keys-p-definition
             bip32-ckd*
             bip32-ckd-priv*
             bip32-ckd-pub*))

  (defrule bip32-valid-keys-p-of-insert-of-rcons
    (implies (and (bip32-path-setp paths)
                  (bip32-valid-keys-p root paths)
                  (in path paths)
                  (ubyte32p index)
                  (not (mv-nth 0 (bip32-ckd* root (rcons index path)))))
             (bip32-valid-keys-p root (insert (rcons index path) paths)))
    :enable bip32-valid-keys-p-definition
    :use (:instance bip32-valid-keys-p-necc
          (path (bip32-valid-keys-p-witness
                 root (insert (rcons index path) paths)))))

  (defrule bip32-valid-keys-p-of-tail
    (implies (and (bip32-path-setp paths)
                  (bip32-valid-keys-p root paths))
             (bip32-valid-keys-p root (tail paths)))
    :expand (bip32-valid-keys-p root (tail paths))
    :enable bip32-valid-keys-p-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-valid-depths-p
  :short "Check if all the key depths in a (tree's) set of paths are valid."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a key is serialized, its depth in the tree is represented in 1 byte.
     Thus, in order for keys to be serializable, the maximum depth must be 255.
     Since the master key has depth 0 [BIP32],
     the depth of a key is the length of the key's path.")
   (xdoc::p
    "When sharing key subtrees as explained in the use cases in [BIP32],
     the root key is not the master key,
     but some descendant of the master key.
     That descendant has a non-0 depth
     in the supertree rooted at the master key.
     Thus, the ``real'' depth of each key in the subtree
     is the depth within the subtree plus the depth of the subtree's root;
     this ``real'' depth is the one in the supertree rooted at the master key.
     The @('init') argument of this function is the depth of the root
     (i.e. the ``initial'' depth);
     this function checks that the depth in the subtree plus @('init')
     does not exceed 255.
     If the subtree coincides with the supertree, then @('init') is 0.")
   (xdoc::p
    "Even though this function is applied to index trees,
     it can be defined on general sets of paths.")
   (xdoc::p
    "We introduce this function as a constrained function,
     so that we can make an executable attachment for it
     (in @('bip32-executable.lisp')).
     Since currently @(tsee std::define-sk) does not support
     @(tsee defun-sk)'s @(':constrain') and
     @(tsee defun-sk) forces the guard to @('t') when @(':constrain') is @('t'),
     we use an @(tsee encapsulate) for now to introduce this function.
     A @(tsee std::define-sk) is used to locally define the witness,
     which also guard-verifies the matrix of the function,
     as additional validation.")
   (xdoc::p
    "The singleton tree consisting of just the root
     (represented as the singleton set consisting of the empty path),
     trivially satisfies this depth validity condition.")
   (xdoc::p
    "Extending a path of an index tree
     preserves the validity of the key depths,
     provided that the depth of the path being extended is below 255.")
   (xdoc::p
    "The tail of a set of paths with valid depths also has all valid depths."))

  (encapsulate
    (((bip32-valid-depths-p * *) => *
      :formals (init paths)
      :guard (and (bytep init) (bip32-path-setp paths)))
     ((bip32-valid-depths-p-witness * *) => *))

    (local
     (define-sk bip32-valid-depths-p ((init bytep) (paths bip32-path-setp))
       :returns (yes/no booleanp :name bip32-valid-depths-p-return-type)
       (forall (path)
               (implies (in path (bip32-path-sfix paths))
                        (bytep (+ (byte-fix init) (len path)))))
       ///
       (fty::deffixequiv-sk bip32-valid-depths-p
         :args ((init bytep) (paths bip32-path-setp)))))

    (defruled bip32-valid-depths-p-definition
      (equal (bip32-valid-depths-p init paths)
             (let ((path (bip32-valid-depths-p-witness init paths)))
               (implies (in path (bip32-path-sfix paths))
                        (bytep (+ (byte-fix init) (len path))))))
      :rule-classes :definition
      :enable bip32-valid-depths-p)

    (defrule booleanp-of-bip32-valid-depths-p
      (booleanp (bip32-valid-depths-p init paths))
      :rule-classes (:rewrite :type-prescription))

    (defruled bip32-valid-depths-p-necc
      (implies (bip32-valid-depths-p init paths)
               (implies (in path (bip32-path-sfix paths))
                        (bytep (+ (byte-fix init) (len path)))))
      :enable bip32-valid-depths-p-necc)

    (fty::deffixequiv bip32-valid-depths-p
      :args ((init bytep) (paths bip32-path-setp))))

  (defrule bip32-valid-depths-p-of-singleton-empty-path
    (bip32-valid-depths-p init '(nil))
    :enable (in bip32-valid-depths-p-definition))

  (defrule bip32-valid-depths-p-of-insert-of-rcons
    (implies (and (bip32-path-setp paths)
                  (bip32-valid-depths-p init paths)
                  (in path paths)
                  (< (+ (byte-fix init) (len path)) 255)
                  (ubyte32p index))
             (bip32-valid-depths-p init (insert (rcons index path) paths)))
    :enable (bytep bip32-valid-depths-p-definition)
    :use ((:instance bip32-valid-depths-p-necc
           (path (bip32-valid-depths-p-witness
                  init (insert (rcons index path) paths))))))

  (defrule bip32-valid-depths-p-of-tail
    (implies (and (bip32-path-setp paths)
                  (bip32-valid-depths-p init paths))
             (bip32-valid-depths-p init (tail paths)))
    :expand (bip32-valid-depths-p init (tail paths))
    :enable bip32-valid-depths-p-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bip32-key-tree
  :short "Key trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "In a key tree, each node is labeled by a key derived from the root key.
     Thus, at the specification level, it suffices to have
     the root key and the underlying index tree,
     since all the non-root keys can be derived.
     We require each non-root key to be valid,
     as defined by @(tsee bip32-valid-keys-p).")
   (xdoc::p
    "In addition to a root key and an index tree,
     our formalization of root keys includes a few other components.
     These are needed in order for the keys in the tree to be serializable
     in the manner specified in [BIP32].")
   (xdoc::p
    "One of these components is the depth of the root key
     with respect to the (super)tree rooted at the master key.
     This is 0 if this tree is rooted at the master key.
     We require each key in this (sub)tree to have a depth below 256,
     taking into account the depth of the root.
     We pass the root depth to @(tsee bip32-valid-depths-p)
     to check this condition.")
   (xdoc::p
    "Another component is the index of the root of this tree
     within the (super)tree rooted at the master key.
     This must be 0 if this tree's root is master key.
     Otherwise, the root of this subtree is some child within the supertree,
     and this component is the index of that child.
     Without this component,
     we would be unable to serialize the root of this subtree.
     Note that the non-root nodes in the tree have known indices.")
   (xdoc::p
    "Yet another component is the fingerprint (consisting of 4 bytes [BIP32])
     of the parent of the key at the root of this tree.
     This must consist of four zeros if this root key is the master key.
     Without this component,
     we would be unable to serialize the root of this subtree.
     Note that the non-root nodes in the tree have parent fingerprints
     that can be calculated from their parent key."))
  ((root-key bip32-ext-key)
   (root-depth byte)
   (root-index ubyte32 :reqfix (if (equal root-depth 0)
                                   0
                                 root-index))
   (root-parent byte-list :reqfix (if (or (equal root-depth 0)
                                          (not (equal (len root-parent) 4)))
                                      (list 0 0 0 0)
                                    root-parent))
   (index-tree bip32-index-tree :reqfix (if (and (bip32-valid-keys-p root-key
                                                                     index-tree)
                                                 (bip32-valid-depths-p root-depth
                                                                       index-tree))
                                            index-tree
                                          (list nil))))
  :require (and (bip32-valid-keys-p root-key index-tree)
                (bip32-valid-depths-p root-depth index-tree)
                (implies (equal root-depth 0)
                         (equal root-index 0))
                (equal (len root-parent) 4)
                (implies (equal root-depth 0)
                         (equal root-parent (list 0 0 0 0))))
  :layout :list
  :pred bip32-key-treep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-key-tree-priv-p ((tree bip32-key-treep))
  :returns (yes/no booleanp)
  :short "Check if a key tree consists of private keys."
  :long
  (xdoc::topstring-p
   "We check whether the root is an extended private key.")
  (bip32-ext-key-case (bip32-key-tree->root-key tree) :priv)
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-path-in-tree-p ((path ubyte32-listp) (tree bip32-key-treep))
  :returns (yes/no booleanp)
  :short "Check if a path designates a key in a key tree."
  :long
  (xdoc::topstring
   (xdoc::p
    "The empty path always designates a key: the one at the root.")
   (xdoc::p
    "If a path designates a key, every prefix of it (taken with @(tsee take))
     also designates an (ancestor) key.")
   (xdoc::p
    "If a path designates a key,
     that key can be successfully derived from the root.")
   (xdoc::p
    "If a path designates a key,
     the total depth of that key (including the root's depth)
     does not exceed 255."))
  (b* ((path (mbe :logic (ubyte32-list-fix path) :exec path)))
    (in path (bip32-key-tree->index-tree tree)))
  :no-function t
  :hooks (:fix)
  ///

  (defrule bip32-path-in-tree-p-of-nil
    (implies (bip32-key-treep tree)
             (bip32-path-in-tree-p nil tree))
    :enable (bip32-key-treep
             bip32-index-treep
             bip32-path-set-closedp-definition
             bip32-key-tree->index-tree))

  (defrule bip32-path-in-tree-p-of-take
    (implies (and (bip32-key-treep tree)
                  (bip32-path-in-tree-p path tree)
                  (<= (nfix n) (len path)))
             (bip32-path-in-tree-p (take n path) tree))
    :use (:instance bip32-path-set-closedp-necc
          (paths (bip32-key-tree->index-tree tree))
          (path (ubyte32-list-fix path))
          (prefix (take n (ubyte32-list-fix path)))))

  (defrule valid-key-when-bip32-path-in-tree-p
    (implies (and (bip32-key-treep tree)
                  (bip32-path-in-tree-p path tree))
             (not (mv-nth 0 (bip32-ckd* (bip32-key-tree->root-key tree) path))))
    :use (:instance bip32-valid-keys-p-necc
          (root (bip32-key-tree->root-key tree))
          (paths (bip32-key-tree->index-tree tree))
          (path (ubyte32-list-fix path))))

  (defrule valid-depth-when-bip32-path-in-tree-p
    (implies (and (bip32-key-treep tree)
                  (bip32-path-in-tree-p path tree))
             (bytep (+ (bip32-key-tree->root-depth tree)
                       (len path))))
    :use (:instance bip32-valid-depths-p-necc
          (init (bip32-key-tree->root-depth tree))
          (paths (bip32-key-tree->index-tree tree))
          (path (ubyte32-list-fix path)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-extend-tree
  ((tree bip32-key-treep) (parent-path ubyte32-listp) (child-index ubyte32p))
  :guard (and (bip32-path-in-tree-p parent-path tree)
              (not (bip32-path-in-tree-p (rcons child-index parent-path) tree))
              (< (+ (bip32-key-tree->root-depth tree) (len parent-path)) 255))
  :returns (mv (error? booleanp)
               (new-tree bip32-key-treep))
  :short "Extend a key tree with a key."
  :long
  (xdoc::topstring
   (xdoc::p
    "The new key is identified by
     (i) the path of its parent and (ii) the child index of the new key.
     The parent must be already in the tree, while the new child key must not:
     this is expressed by the guard of this function.
     The total depth of the new key should not exceed 255:
     this is also expressed by the guard.")
   (xdoc::p
    "Given our model of key trees,
     we just add the path of the new key to the underlying index tree.
     But we need to check whether the child key derivation fails:
     if it does, we return the input key tree unchanged,
     along with @('t') as the first result.
     The first result is @('nil') if key derivation succeeds.")
   (xdoc::p
    "If the key tree consists of private keys, the new key is private.
     If the key tree consists of public keys, the new key is public.
     We uniformly use the @(tsee bip32-ckd) function."))
  (b* ((tree (mbe :logic (bip32-key-tree-fix tree) :exec tree))
       (parent-path (mbe :logic (ubyte32-list-fix parent-path)
                         :exec parent-path))
       (child-index (mbe :logic (ubyte32-fix child-index) :exec child-index))
       ((bip32-key-tree tree) tree)
       ((unless (mbt (bip32-path-in-tree-p parent-path tree))) (mv t tree))
       (new-path (rcons child-index parent-path))
       ((unless (mbt (not (bip32-path-in-tree-p new-path tree)))) (mv t tree))
       ((unless (mbt
                 (< (+ tree.root-depth (len parent-path)) 255))) (mv t tree))
       ((mv error? &) (bip32-ckd* tree.root-key new-path))
       ((when error?) (mv error? tree))
       (new-index-tree (insert new-path tree.index-tree))
       (new-tree (change-bip32-key-tree tree :index-tree new-index-tree)))
    (mv nil new-tree))
  :no-function t
  :guard-hints (("Goal" :in-theory (enable bip32-path-in-tree-p)))
  :hooks (:fix)
  ///

  (defrule bip32-key-tree->root-key-of-bip32-extend-tree
    (equal (bip32-key-tree->root-key
            (mv-nth 1 (bip32-extend-tree tree parent-path child-index)))
           (bip32-key-tree->root-key tree)))

  (defrule bip32-key-tree->root-depth-of-bip32-extend-tree
    (equal (bip32-key-tree->root-depth
            (mv-nth 1 (bip32-extend-tree tree parent-path child-index)))
           (bip32-key-tree->root-depth tree)))

  (defrule bip32-key-tree->root-index-of-bip32-extend-tree
    (equal (bip32-key-tree->root-index
            (mv-nth 1 (bip32-extend-tree tree parent-path child-index)))
           (bip32-key-tree->root-index tree)))

  (defrule bip32-key-tree->root-parent-of-bip32-extend-tree
    (equal (bip32-key-tree->root-parent
            (mv-nth 1 (bip32-extend-tree tree parent-path child-index)))
           (bip32-key-tree->root-parent tree)))

  (defrule bip32-key-tree->index-tree-of-bip32-extend-tree
    (b* (((mv error? tree1) (bip32-extend-tree tree parent-path child-index)))
      (equal (bip32-key-tree->index-tree tree1)
             (if error?
                 (bip32-key-tree->index-tree tree)
               (insert (rcons (ubyte32-fix child-index)
                              (ubyte32-list-fix parent-path))
                       (bip32-key-tree->index-tree tree)))))
    :enable bip32-path-in-tree-p)

  (defrule bip32-key-tree-priv-p-of-bip32-extend-tree
    (equal (bip32-key-tree-priv-p
            (mv-nth 1 (bip32-extend-tree tree parent-path child-index)))
           (bip32-key-tree-priv-p tree))
    :enable bip32-key-tree-priv-p)

  (defrule bip32-path-in-tree-p-of-bip32-extend-tree
    (b* (((mv error? new-key-tree) (bip32-extend-tree key-tree path index)))
      (implies (not error?)
               (bip32-path-in-tree-p (rcons index path) new-key-tree)))
    :enable bip32-path-in-tree-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-get-priv-key-at-path ((tree bip32-key-treep) (path ubyte32-listp))
  :guard (and (bip32-path-in-tree-p path tree)
              (bip32-key-tree-priv-p tree))
  :returns (key secp256k1-priv-key-p)
  :short "Retrieve the private key designated by a path in a key tree."
  :long
  (xdoc::topstring-p
   "The tree must consist of private keys, as expressed by the guard.")
  (b* ((root-extkey (bip32-key-tree->root-key tree))
       (root-extprivkey (bip32-ext-key-priv->get root-extkey))
       ((mv error? extprivkey) (bip32-ckd-priv* root-extprivkey path))
       ((unless (mbt (not error?))) (b* ((irrelevant 1)) irrelevant))
       (privkey (bip32-ext-priv-key->key extprivkey)))
    privkey)
  :no-function t
  :guard-hints (("Goal"
                 :use valid-key-when-bip32-path-in-tree-p
                 :in-theory (enable bip32-ckd* bip32-key-tree-priv-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-get-pub-key-at-path ((tree bip32-key-treep) (path ubyte32-listp))
  :guard (bip32-path-in-tree-p path tree)
  :returns (key secp256k1-pub-key-p)
  :short "Retrieven the public key designated by a path in a key tree."
  :long
  (xdoc::topstring-p
   "The tree may consist of private or public keys.")
  (b* ((root-extkey (bip32-key-tree->root-key tree))
       ((mv error? extkey) (bip32-ckd* root-extkey path))
       ((unless (mbt (not error?)))
        (b* ((irrelevant (secp256k1-priv-to-pub 1))) irrelevant)))
    (bip32-ext-key-case
     extkey
     :priv (b* ((extprivkey (bip32-ext-key-priv->get extkey))
                (privkey (bip32-ext-priv-key->key extprivkey))
                (pubkey (secp256k1-priv-to-pub privkey)))
             pubkey)
     :pub (b* ((extpubkey (bip32-ext-key-pub->get extkey))
               (pubkey (bip32-ext-pub-key->key extpubkey)))
            pubkey)))
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bip32-key-serialization
  :parents (bip32)
  :short "Key serialization."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-key-identifier ((key bip32-ext-key-p))
  :returns (id byte-listp)
  :short "Identifier of an extended key."
  :long
  (xdoc::topstring
   (xdoc::p
    "The section `Key identifiers' of [BIP32] says that
     an extended key is identified by
     the Hash160 of the serialized elliptic curve public key,
     ignoring the chain code..")
   (xdoc::p
    "This should apply to both private and public keys.
     If given a private key, we calculate the corresponding public key."))
  (b* ((pubkey (bip32-ext-key-case
                key
                :priv (secp256k1-priv-to-pub (bip32-ext-priv-key->key key.get))
                :pub (bip32-ext-pub-key->key key.get)))
       (serialized (secp256k1-point-to-bytes pubkey t)))
    (hash160 serialized))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (id (equal (len id) 20) :name len-of-bip32-key-identifier)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-key-fingerprint ((key bip32-ext-key-p))
  :returns (fp byte-listp)
  :short "Fingerprint of an extended key."
  :long
  (xdoc::topstring
   (xdoc::p
    "The section `Key identifiers' of [BIP32]
     says that the first 32 bits (i.e. 4 bytes) of a key identifier
     are the key fingerprint."))
  (take 4 (bip32-key-identifier key))
  :no-function t
  :hooks (:fix)
  ///

  (more-returns
   (fp (equal (len fp) 4) :name len-of-bip32-key-fingerprint)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-serialization-versions
  :short "Versions bytes for serializing extended keys."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are for private or public keys, for mainnet or testnet:
     four possible combinations.")
   (xdoc::p
    "The values are specified in [BIP32],
     as hexadecimal integers,
     so we introduce them as such here.
     Even though [BIP32] does not explicitly say
     how these (32-bit) integers are converted to bytes,
     it seems reasonable that they are converted as big endian.
     This could be also confirmed by verifying that,
     after Base58 encoding,
     the serialized keys start with
     @('xprv'), @('xpub'), @('tprv'), and @('tpub')."))

  (defval *bip32-version-priv-main*
    :parents (bip32-serialization-versions)
    #x0488ADE4
    ///
    (assert-event (ubyte32p *bip32-version-priv-main*)))

  (defval *bip32-version-pub-main*
    :parents (bip32-serialization-versions)
    #x0488B21E
    ///
    (assert-event (ubyte32p *bip32-version-pub-main*)))

  (defval *bip32-version-priv-test*
    :parents (bip32-serialization-versions)
    #x04358394
    ///
    (assert-event (ubyte32p *bip32-version-priv-test*)))

  (defval *bip32-version-pub-test*
    :parents (bip32-serialization-versions)
    #x043587CF
    ///
    (assert-event (ubyte32p *bip32-version-pub-test*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-serialize-key ((key bip32-ext-key-p)
                             (depth bytep)
                             (index ubyte32p)
                             (parent (and (byte-listp parent)
                                          (equal (len parent) 4)))
                             (mainnet? booleanp))
  :guard (implies (equal depth 0)
                  (and (equal index 0)
                       (equal parent (list 0 0 0 0))))
  :returns (bytes byte-listp)
  :short "Serialize an extended key."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the key, from which chain code and key data are obtained,
     this function takes additional arguments necessary for
     a complete serialization as specified in [BIP32].")
   (xdoc::p
    "If the depth is 0, this is the master key and thus
     the child number and the parent's fingerprint
     must be 0 too [BIP32].
     This is expressed by the guard.")
   (xdoc::p
    "A boolean argument says whether the key is being serialized for
     the mainnet (if @('t')) or for the testnet (if @('nil'))."))
  (b* ((depth (mbe :logic (byte-fix depth) :exec depth))
       (index (mbe :logic (ubyte32-fix index) :exec index))
       (parent (mbe :logic (byte-list-fix parent) :exec parent))
       (parent (mbe :logic (if (= (len parent) 4)
                               parent
                             (list 0 0 0 0))
                    :exec parent))
       ((mv key-data chain-code version)
        (bip32-ext-key-case
         key
         :priv (mv (cons 0 (nat=>bebytes 32 (bip32-ext-priv-key->key key.get)))
                   (bip32-ext-priv-key->chain-code key.get)
                   (if mainnet?
                       *bip32-version-priv-main*
                     *bip32-version-priv-test*))
         :pub (mv (secp256k1-point-to-bytes
                   (bip32-ext-pub-key->key key.get) t)
                  (bip32-ext-pub-key->chain-code key.get)
                  (if mainnet?
                      *bip32-version-pub-main*
                    *bip32-version-pub-test*)))))
    (append (nat=>bebytes 4 version)
            (list depth)
            parent
            (nat=>bebytes 4 index)
            chain-code
            key-data))
  :guard-hints (("Goal" :in-theory (enable ubyte32p)))
  :no-function t
  :hooks (:fix)

  ///
  (more-returns
   (bytes (equal (len bytes) 78) :name len-of-bip32-serialize-key)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip32-serialized-key-p ((bytes byte-listp))
  :returns (yes/no booleanp)
  :short "Check if a sequence of bytes is a serialized extended key."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a declarative, non-executable definition,
     which essentially characterizes the image of @(tsee bip32-serialize-key)
     over arguments that satisfy that function's guard.")
   (xdoc::p
    "By definition,
     the witness function is the right inverse of @(tsee bip32-serialize-key),
     over valid serialized keys."))
  (exists (key depth index parent mainnet?)
          (and (bip32-ext-key-p key)
               (bytep depth)
               (ubyte32p index)
               (byte-listp parent)
               (equal (len parent) 4)
               (booleanp mainnet?)
               (implies (equal depth 0)
                        (and (equal index 0)
                             (equal parent (list 0 0 0 0))))
               (equal (bip32-serialize-key key depth index parent mainnet?)
                      (byte-list-fix bytes))))
  :skolem-name bip32-serialized-key-witness
  ///

  (fty::deffixequiv-sk bip32-serialized-key-p
    :args ((bytes byte-listp)))

  (defrule bip32-ext-key-p-of-mv-nth-0-of-bip32-serialized-key-witness
    (implies (bip32-serialized-key-p bytes)
             (bip32-ext-key-p
              (mv-nth 0 (bip32-serialized-key-witness bytes)))))

  (defrule bytep-of-mv-nth-1-of-bip32-serialized-key-witness
    (implies (bip32-serialized-key-p bytes)
             (bytep
              (mv-nth 1 (bip32-serialized-key-witness bytes)))))

  (defrule ubyte32p-of-mv-nth-2-of-bip32-serialized-key-witness
    (implies (bip32-serialized-key-p bytes)
             (ubyte32p
              (mv-nth 2 (bip32-serialized-key-witness bytes)))))

  (defrule byte-listp-of-mv-nth-3-of-bip32-serialized-key-witness
    (implies (bip32-serialized-key-p bytes)
             (byte-listp
              (mv-nth 3 (bip32-serialized-key-witness bytes)))))

  (defrule len-of-mv-nth-3-of-bip32-serialize-key-witness
    (implies (bip32-serialized-key-p bytes)
             (equal (len (mv-nth 3 (bip32-serialized-key-witness bytes)))
                    4)))

  (defrule booleanp-of-mv-nth-4-of-bip32-serialized-key-witness
    (implies (bip32-serialized-key-p bytes)
             (booleanp
              (mv-nth 4 (bip32-serialized-key-witness bytes)))))

  (defrule depth-index-parent-constraint-of-bip32-serialized-key-witness
    (implies (and (bip32-serialized-key-p bytes)
                  (equal (mv-nth 1 (bip32-serialized-key-witness bytes))
                         0))
             (and (equal (mv-nth 2 (bip32-serialized-key-witness bytes))
                         0)
                  (equal (mv-nth 3 (bip32-serialized-key-witness bytes))
                         (list 0 0 0 0)))))

  (defrule bip32-serialize-key-of-bip32-serialized-key-witness
    (implies (bip32-serialized-key-p bytes)
             (b* (((mv key depth index parent mainnet?)
                   (bip32-serialized-key-witness bytes)))
               (equal (bip32-serialize-key key depth index parent mainnet?)
                      (byte-list-fix bytes)))))

  (defrule bip32-serialized-key-p-of-bip32-serialize-key
    (implies (and (bip32-ext-key-p key)
                  (bytep depth)
                  (ubyte32p index)
                  (byte-listp parent)
                  (equal (len parent) 4)
                  (booleanp mainnet?)
                  (implies (equal depth 0)
                           (and (equal index 0)
                                (equal parent (list 0 0 0 0)))))
             (bip32-serialized-key-p
              (bip32-serialize-key key depth index parent mainnet?)))
    :use (:instance bip32-serialized-key-p-suff
          (bytes (bip32-serialize-key key depth index parent mainnet?)))
    :disable (bip32-serialized-key-p bip32-serialized-key-p-suff)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-deserialize-key ((bytes byte-listp))
  :returns (mv (error? booleanp)
               (key bip32-ext-key-p)
               (depth bytep)
               (index ubyte32p)
               (parent (and (byte-listp parent)
                            (equal (len parent) 4)))
               (mainnet? booleanp))
  :short "Deserialize an extended key."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is declaratively specified as the inverse of serialization.")
   (xdoc::p
    "The first result is @('t')
     if the input bytes are not a serialized key;
     in this case, the other results are irrelevant.
     Otherwise, the first result is @('nil') (i.e. no error)
     and the constituents of the the serialized key are returned;
     these correspond to the inputs of @(tsee bip32-serialize-key).")
   (xdoc::p
    "We prove that deserialization is the right inverse of serialization.
     To prove that it is also left inverse,
     we need to prove the injectivity of serialization first.
     This will be done soon."))
  (b* ((bytes (byte-list-fix bytes)))
    (if (bip32-serialized-key-p bytes)
        (b* (((mv key depth index parent mainnet?)
              (bip32-serialized-key-witness bytes)))
          (mv nil key depth index parent mainnet?))
      (b* ((irrelevant-key
            (bip32-ext-key-priv (bip32-ext-priv-key 1 (repeat 32 0)))))
        (mv t irrelevant-key 0 0 (list 0 0 0 0) nil))))
  :no-function t
  :hooks (:fix)
  ///

  (defrule not-mv-nth-0-of-bip32-deserialize-key-when-bip32-serialized-key-p
    (implies (bip32-serialized-key-p bytes)
             (not (mv-nth 0 (bip32-deserialize-key bytes)))))

  (defrule bip32-ext-key-p-of-mv-nth-1-of-bip32-deserialize-key
    (bip32-ext-key-p (mv-nth 1 (bip32-deserialize-key bytes))))

  (defrule bytep-of-mv-nth-2-of-bip32-deserialize-key
    (bytep (mv-nth 2 (bip32-deserialize-key bytes))))

  (defrule ubyte32p-of-mv-nth-3-of-bip32-deserialize-key
    (ubyte32p (mv-nth 3 (bip32-deserialize-key bytes))))

  (defrule byte-listp-of-mv-nth-4-of-bip32-deserialize-key
    (byte-listp (mv-nth 4 (bip32-deserialize-key bytes))))

  (defrule len-of-mv-nth-4-of-bip32-serialize-key-witness
    (equal (len (mv-nth 4 (bip32-deserialize-key bytes)))
           4))

  (defrule booleanp-of-mv-nth-5-of-bip32-deserialize-key
    (booleanp (mv-nth 5 (bip32-deserialize-key bytes))))

  (defrule depth-index-parent-constraint-of-bip32-deserialize-key
    (implies (equal (mv-nth 2 (bip32-deserialize-key bytes))
                    0)
             (and (equal (mv-nth 3 (bip32-deserialize-key bytes))
                         0)
                  (equal (mv-nth 4 (bip32-deserialize-key bytes))
                         (list 0 0 0 0)))))

  (defrule bip32-serialize-key-of-bip32-deserialize-key
    (implies (bip32-serialized-key-p bytes)
             (b* (((mv error? key depth index parent mainnet?)
                   (bip32-deserialize-key bytes)))
               (and (not error?)
                    (equal (bip32-serialize-key key depth index parent mainnet?)
                           (byte-list-fix bytes)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-export-key ((tree bip32-key-treep)
                          (path ubyte32-listp)
                          (mainnet? booleanp)
                          (public? booleanp))
  :guard (and (bip32-path-in-tree-p path tree)
              (or public? (bip32-key-tree-priv-p tree)))
  :returns (exported byte-listp)
  :short "Export a key from a tree."
  :long
  (xdoc::topstring
   (xdoc::p
    "The key to export is designated by a path,
     which must be a valid path in the tree.")
   (xdoc::p
    "A boolean argument specifies whether the key is
     for the mainnet or for the testnet.")
   (xdoc::p
    "Another boolean argument specified whether the key should be public.
     If this is @('nil'), then the tree must consist of private keys,
     as expressed by the guard.
     If this is @('t') instead, the tree may consist of private or public keys;
     if it consists of private keys,
     we use @(tsee bip32-n) to turn the extended private key at the path
     into the corresponding extended public key,
     prior to serializing it.")
   (xdoc::p
    "We first derive the key at the path from the root, via @(tsee bip32-ckd*).
     Since the key tree satisfies @(tsee bip32-valid-keys-p)
     and the path is in the tree,
     this never returns an error, as proved via @(tsee mbt) below.")
   (xdoc::p
    "We calculate the total depth of the key
     by adding the length of the path to the root's depth.
     Since the key tree satisfies @(tsee bip32-valid-depths-p)
     and the path is in the tree,
     this never exceeds 255 (i.e. always fits in a byte),
     as proved via @(tsee mbt) below.")
   (xdoc::p
    "The index of the key is
     the last element of the path if the path is not empty.
     Otherwise, it is the index of the root.")
   (xdoc::p
    "The parent key's fingerprint is
     calculated from the parent key if the path is not empty.
     The path of the parent is obtained
     by removing the last element from the path of the key:
     since this is also a path in the tree,
     the call of @(tsee bip32-ckd*) on the parent's path
     does not return an error either, as proved via @(tsee mbt) below.
     Otherwise, if the path is empty,
     we obtain the parent's fingerprint from the root of the tree.")
   (xdoc::p
    "With all the above pieces of data in hand,
     we serialize the key, completing the export."))
  (b* ((path (mbe :logic (ubyte32-list-fix path) :exec path))
       ((bip32-key-tree tree) tree)
       ((mv error? key) (bip32-ckd* tree.root-key path))
       ((unless (mbt (not error?))) nil)
       (key (if (and public?
                     (bip32-key-tree-priv-p tree))
                (bip32-ext-key-pub (bip32-n (bip32-ext-key-priv->get key)))
              key))
       (depth (+ tree.root-depth (len path)))
       ((unless (mbt (bytep depth))) nil)
       (index (if (consp path)
                  (car (last path))
                tree.root-index))
       (parent (if (consp path)
                   (b* ((parent-path (butlast path 1))
                        ((mv error? parent-key)
                         (bip32-ckd* tree.root-key parent-path))
                        ((unless (mbt (not error?))) nil))
                     (bip32-key-fingerprint parent-key))
                 tree.root-parent)))
    (bip32-serialize-key key depth index parent mainnet?))
  :no-function t
  :guard-hints (("Goal" :in-theory (enable bip32-key-tree-priv-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-import-key ((bytes byte-listp))
  :returns (mv (error? booleanp)
               (tree bip32-key-treep)
               (mainnet? booleanp))
  :short "Import a key into a tree."
  :long
  (xdoc::topstring
   (xdoc::p
    "We deserialize the key into its components,
     which we use to construct a singleton key tree
     that contains just that key.")
   (xdoc::p
    "The boolean flag that distinguishes mainnet from testnet,
     returned by serialization,
     is not used to construct the tree.
     We return this flag as an additional result.")
   (xdoc::p
    "If deserialization fails,
     the first result is @('t'),
     which signals an error.
     In this case, the second and third results are irrelevant."))
  (b* (((mv error? key depth index parent mainnet?)
        (bip32-deserialize-key bytes))
       (tree (bip32-key-tree key depth index parent '(nil))))
    (mv error? tree mainnet?))
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bip32-master-key-generation
  :parents (bip32)
  :short "Master key generation."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-master-key ((seed byte-listp))
  :guard (and (<= 16 (len seed))
              (<= (len seed) 64))
  :returns (mv (error? booleanp)
               (key bip32-ext-priv-key-p))
  :short "Generate a master key from a seed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The exact generation of the seed is not specified in [BIP32],
     so it is an input to this function.")
   (xdoc::p
    "[BIP32] constrains the length of the seed in bits,
     namely to be between 128 and 512 bits.
     In principle, the seed could consist of a number of bits
     that is not a multiple of 8,
     but this seems unlikely in practice:
     that is, the seed will likey consist of a number of whole bytes.
     The number of whole bytes must be therefore between 16 and 64.")
   (xdoc::p
    "The key for HMAC-SHA-512 is shown as the string
     @('\"Bitcoin seed\"') in [BIP32].
     It seems reasonable to regard that as the list of bytes
     consisting of the ASCII codes of the characters in the string,
     in the order in which they appear in the string.")
   (xdoc::p
    "If the calculated private key is invalid as specified in [BIP32],
     we return an error flag as the first result;
     in this case, the second result (the key) is irrelevant).
     Otherwise, the first result is @('nil'), i.e. no error."))
  (b* ((hmac-key (string=>nats "Bitcoin seed"))
       (hmac-data seed)
       (big-i (hmac-sha-512 hmac-key hmac-data))
       (big-i-l (take 32 big-i))
       (big-i-r (nthcdr 32 big-i))
       (parsed-big-i-l (bebytes=>nat big-i-l))
       (n (secp256k1-order))
       ((when (or (= parsed-big-i-l 0)
                  (>= parsed-big-i-l n)))
        (b* ((irrelevant-ext-key (bip32-ext-priv-key 1 big-i-r)))
          (mv t irrelevant-ext-key)))
       (ext-key (bip32-ext-priv-key parsed-big-i-l big-i-r)))
    (mv nil ext-key))
  :no-function t
  :prepwork ((local (include-book "std/lists/nthcdr" :dir :system)))
  :guard-hints (("Goal"
                 :in-theory (enable secp256k1-priv-key-p
                                    bip32-chain-code-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-master-tree ((seed byte-listp))
  :guard (and (<= 16 (len seed))
              (<= (len seed) 64))
  :returns (mv (error? booleanp)
               (tree bip32-key-treep))
  :short "Generate a key tree with (just) a master key from a seed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee bip32-master-key) from a single key
     to a singleton tree containing the key at the root,
     as a master key."))
  (b* (((mv error? key) (bip32-master-key seed))
       (tree (bip32-key-tree (bip32-ext-key-priv key)
                             0
                             0
                             (list 0 0 0 0)
                             '(nil))))
    (mv error? tree))
  :no-function t
  :hooks (:fix)
  ///

  (defrule bip32-key-tree->root-key-of-bip32-master-tree
    (equal (bip32-key-tree->root-key (mv-nth 1 (bip32-master-tree seed)))
           (bip32-ext-key-priv
            (mv-nth 1 (bip32-master-key seed)))))

  (defrule bip32-key-tree->root-depth-of-bip32-master-tree
    (equal (bip32-key-tree->root-depth (mv-nth 1 (bip32-master-tree seed)))
           0))

  (defrule bip32-key-tree->root-index-of-bip32-master-tree
    (equal (bip32-key-tree->root-index (mv-nth 1 (bip32-master-tree seed)))
           0))

  (defrule bip32-key-tree->root-parent-of-bip32-master-tree
    (equal (bip32-key-tree->root-parent (mv-nth 1 (bip32-master-tree seed)))
           (list 0 0 0 0)))

  (defrule bip32-key-tree->index-tree-of-bip32-master-tree
    (equal (bip32-key-tree->index-tree (mv-nth 1 (bip32-master-tree seed)))
           (list nil)))

  (defrule bip32-key-tree-priv-p-of-bip32-master-tree
    (bip32-key-tree-priv-p (mv-nth 1 (bip32-master-tree seed)))
    :enable bip32-key-tree-priv-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bip32-wallet-structure
  :parents (bip32)
  :short "Wallet structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "[BIP32] describes a recommended structure for the key tree.
     This is illustrated in a figure in [BIP32],
     an explained in Section `Specification: Wallet structure' of [BIP32].")
   (xdoc::p
    "According to the figure, each key in the tree has depth 0, 1, 2, or 3.
     The master key is at depth 0, as always.
     The keys at depth 1 are account keys, one per account.
     The keys at depth 2 are chain keys, one per chain.
     The keys at depth 3 are account keys, one per account.")
   (xdoc::p
    "We formalize this structure as a predicate over key trees.
     With that in hand, we can formally say whether
     (the key tree of) a wallet is compliant with this structure or not.
     This compliance predicate is defined incrementally below."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip32-compliant-depth-p ((tree bip32-key-treep))
  :returns (yes/no booleanp)
  :short "Check if the depth of a key tree
          complies with the BIP 32 wallet structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to the figure in [BIP32],
     the key tree stops at depth 3,
     i.e. the address keys have no children
     (and therefore no grandchildren, great-grandchildren, etc.).
     This is formally expressed by saying that
     every path in the tree has a length below 4."))
  (forall (path)
          (implies (and (ubyte32-listp path)
                        (bip32-path-in-tree-p path tree))
                   (< (len path) 4)))
  ///

  (fty::deffixequiv-sk bip32-compliant-depth-p
    :args ((tree bip32-key-treep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip32-compliant-addresses-for-limit-p ((tree bip32-key-treep)
                                                  (account-index ubyte32p)
                                                  (chain-index ubyte32p)
                                                  (address-index-limit natp))
  :guard (bip32-path-in-tree-p (list account-index chain-index) tree)
  :returns (yes/no booleanp)
  :short "Check if the address keys under a given chain key in a tree
          comply with the BIP 32 wallet structure,
          for a given address index limit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The chain key is identified by an account index and a chain index,
     passed as arguments to this predicate.
     This predicate essentially checks if the designated chain key
     has children at all the indices below a limit
     (passed as another argument to this predicate),
     and has no other children.")
   (xdoc::p
    "The adverb 'essentially' above refers to the fact that
     a child key derivation may fail,
     and so there may be rare but mathematically possible gaps
     in the sequence of address keys.
     The address index limit passed as argument is often
     the number of address keys under the chain key,
     except for the rare cases in which there are gaps,
     or in another case described below.")
   (xdoc::p
    "Note that the guard of this predicate requires the chain key to be valid.
     Therefore @(tsee bip32-ckd*), as used in the definition of this predicate,
     returns an error iff the address key is invalid,
     i.e. iff there is an unavoidable gap in the sequence of address keys.
     Formally, we require that
     each address key path whose address index is below the limit
     either is in the tree or corresponds to an invalid address key.")
   (xdoc::p
    "If the address index limit is 0,
     this predicate holds iff the chain key has no children.
     This corresponds to the valid situation in which,
     in a compliant wallet,
     a chain key has been created,
     but no address keys under it have been created yet.")
   (xdoc::p
    "The guard of this predicate allows the address index limit to be
     any natural number, not necessarily representable in 32 bits like indices.
     Thus, the unlikely but mathematically possible case in which
     all possible address keys have been created under a chain key,
     can be accommodated by using @($2^{32}$) (or any larger number)
     as address index limit.
     If the address index limit is larger than @($2^{32}$),
     then the address index limit is definitely not the number of address keys,
     even if there are no gaps in the address keys."))
  (forall (address-index)
          (implies (ubyte32p address-index)
                   (b* ((path (list account-index
                                    chain-index
                                    address-index)))
                     (if (< address-index (nfix address-index-limit))
                         (or (bip32-path-in-tree-p path tree)
                             (mv-nth 0 (bip32-ckd*
                                        (bip32-key-tree->root-key tree)
                                        path)))
                       (not (bip32-path-in-tree-p path tree))))))
  ///

  (fty::deffixequiv-sk bip32-compliant-addresses-for-limit-p
    :args ((tree bip32-key-treep)
           (account-index ubyte32p)
           (chain-index ubyte32p)
           (address-index-limit natp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip32-compliant-addresses-p ((tree bip32-key-treep)
                                        (account-index ubyte32p)
                                        (chain-index ubyte32p))
  :guard (bip32-path-in-tree-p (list account-index chain-index) tree)
  :returns (yes/no booleanp)
  :short "Check if the address keys under a given chain key in a tree
          comply with the BIP 32 wallet structure."
  :long
  (xdoc::topstring-p
   "This is obtained by existentially quantifying the address index limit
    in @(tsee bip32-compliant-addresses-for-limit-p).
    See the documentation of that function for details.")
  (exists (address-index-limit)
          (and (natp address-index-limit)
               (bip32-compliant-addresses-for-limit-p
                tree account-index chain-index address-index-limit)))
  ///

  (fty::deffixequiv-sk bip32-compliant-addresses-p
    :args ((tree bip32-key-treep)
           (account-index ubyte32p)
           (chain-index ubyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip32-compliant-chains-p ((tree bip32-key-treep)
                                     (account-index ubyte32p))
  :guard (bip32-path-in-tree-p (list account-index) tree)
  :returns (yes/no booleanp)
  :short "Check if the chain keys under a given account key in a tree
          comply with the BIP 32 wallet structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee bip32-compliant-addresses-p)
     and @(tsee bip32-compliant-addresses-for-limit-p),
     but the limit is always 2 in this case,
     because there must be exactly two chains for each account:
     an external chain and an internal chain.
     So we do not need the existential quantification over the limit
     and we just have a single level of (universal) quantification.")
   (xdoc::p
    "There is also another difference with address keys,
     namely that we require both chain keys to be present.
     While an invalid address key is acceptable and is simply skipped,
     we cannot skip an external or internal chain for an account.
     If either chain key is invalid,
     then presumably the whole account key should be skipped;
     this is not explicitly said in [BIP32], but it seems reasonable.")
   (xdoc::p
    "Furthermore, in this predicate we require the address keys under each chain
     to be compliant with the BIP 32 structure.
     We are defining key tree compliance incrementally here."))
  (forall (chain-index)
          (implies (ubyte32p chain-index)
                   (b* ((path (list account-index chain-index)))
                     (case chain-index
                       (0 (and (bip32-path-in-tree-p path tree)
                               (bip32-compliant-addresses-p
                                tree account-index chain-index)))
                       (1 (and (bip32-path-in-tree-p path tree)
                               (bip32-compliant-addresses-p
                                tree account-index chain-index)))
                       (t (not (bip32-path-in-tree-p path tree)))))))
  ///

  (fty::deffixequiv-sk bip32-compliant-chains-p
    :args ((tree bip32-key-treep) (account-index ubyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip32-compliant-accounts-for-limit-p ((tree bip32-key-treep)
                                                 (account-index-limit natp))
  :returns (yes/no booleanp)
  :short "Check if the account keys in a tree
          comply with the BIP 32 wallet structure,
          for a given account index limit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee bip32-compliant-addresses-for-limit-p).")
   (xdoc::p
    "The figure in [BIP32] shows account keys as non-hardned keys,
     because there are no @($\\mathsf{H}$) subscripts in the indices.
     However, the text in [BIP32] shows the @($\\mathsf{H}$) subscripts.
     It seems reasonable for account keys to be hardened,
     so we require that in this predicate.
     Specifically, we require all non-hardened account keys to be absent
     and we apply the limit to hardened account keys
     by adding @($2^{31}$) to the limit.")
   (xdoc::p
    "For each account index below the limit,
     we require not only the account key to be present,
     but also the chain keys to be compliant to the BIP 32 wallet structure;
     again, we are defining compliance incrementally.")
   (xdoc::p
    "We allow a gap in the account keys only if
     the account key is invalid,
     or any chain key under it is invalid.
     See the discussion about this in @(tsee bip32-compliant-chains-p)."))
  (forall (account-index)
          (implies (ubyte32p account-index)
                   (b* ((root-key (bip32-key-tree->root-key tree))
                        (path (list account-index)))
                     (cond ((< account-index (expt 2 31))
                            (not (bip32-path-in-tree-p path tree)))
                           ((< account-index (+ (nfix account-index-limit)
                                                (expt 2 31)))
                            (or (and (bip32-path-in-tree-p path tree)
                                     (bip32-compliant-chains-p
                                      tree account-index))
                                (mv-nth 0 (bip32-ckd* root-key path))
                                (mv-nth 0 (bip32-ckd* root-key
                                                      (rcons 0 path)))
                                (mv-nth 0 (bip32-ckd* root-key
                                                      (rcons 1 path)))))
                           (t (not (bip32-path-in-tree-p path tree)))))))
  ///

  (fty::deffixequiv-sk bip32-compliant-accounts-for-limit-p
    :args ((tree bip32-key-treep) (account-index-limit natp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip32-compliant-accounts-p ((tree bip32-key-treep))
  :returns (yes/no booleanp)
  :short "Check if the account keys in a tree
          comply with the BIP 32 wallet structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee bip32-compliant-addresses-p)."))
  (exists (account-index-limit)
          (and (natp account-index-limit)
               (bip32-compliant-accounts-for-limit-p tree account-index-limit)))
  ///

  (fty::deffixequiv-sk bip32-compliant-accounts-p
    :args ((tree bip32-key-treep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-compliant-tree-p ((tree bip32-key-treep))
  :returns (yes/no booleanp)
  :short "Check if a key tree complies with the BIP 32 wallet structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides requiring the account keys to comply
     (which includes the compliance of the chain and address keys),
     we also require the tree to be rooted at the master private key.
     That is, we exclude subtrees of the master tree
     used for partial sharing.")
   (xdoc::p
    "We also require the tree to have depth below 4."))
  (and (bip32-compliant-accounts-p tree)
       (equal 0 (bip32-key-tree->root-depth tree))
       (bip32-key-tree-priv-p tree)
       (bip32-compliant-depth-p tree))
  :no-function t
  :hooks (:fix))
