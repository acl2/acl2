; Bitcoin -- Bitcoin Improvement Proposal (BIP) 32
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "kestrel/utilities/define-sk" :dir :system)
(include-book "kestrel/utilities/defset" :dir :system)
(include-book "kestrel/utilities/fixbytes/ubyte32-list" :dir :system)

(include-book "crypto")

(local (include-book "std/lists/prefixp" :dir :system))

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
     "@($\\mathsf{parse}_{256}$) is @(tsee bendian=>nat) with base 256.")))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-chain-code
  :short "Chain codes."
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
               (byte-listp cc)))

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
  :short "Extended private keys."
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
  :short "Extended public keys."
  :long
  "<p>
   An extended public key consists of a public key and a chain code.
   </p>"
  ((key secp256k1-pub-key)
   (chain-code bip32-chain-code))
  :layout :list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum bip32-ext-key
  :short "Extended keys (private or public)."
  :long
  "<p>
   This is the (disjoint) union of extended private and public keys.
   </p>"
  (:priv ((get bip32-ext-priv-key)))
  (:pub ((get bip32-ext-pub-key))))

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

(define bip32-ckd ((parent bip32-ext-key-p) (i ubyte32p))
  :returns (mv (error? booleanp)
               (child bip32-ext-key-p))
  :short "Child key derivation from parent key."
  :long
  (xdoc::topapp
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
  :short "Paths in key trees."
  :long
  (xdoc::topapp
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
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset bip32-path-set
  :elt-type ubyte32-list
  :pred bip32-path-setp
  :short "Osets of paths in key trees."
  :long
  (xdoc::topapp
   (xdoc::p
    "At any point in time, a system (e.g. wallet) contains
     a relatively small subset
     of the complete tree of possible keys derived from a root.
     We represent the current tree as a finite set of paths
     that satisfies additional conditions explicated later.")))

(defsection bip32-path-set-ext
  :extension bip32-path-set

  (defrule bip32-path-setp-of-tail
    (implies (bip32-path-setp x)
             (bip32-path-setp (set::tail x)))
    :enable (bip32-path-setp set::tail))

  (defrule ubyte32-listp-when-in-bip32-path-setp
    (implies (and (bip32-path-setp x)
                  (set::in a x))
             (ubyte32-listp a))
    :enable (bip32-path-setp set::in set::head)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip32-path-set-closedp ((paths bip32-path-setp))
  :returns (yes/no booleanp)
  :short "Check if a set of key tree paths is closed under prefix."
  :long
  (xdoc::topapp
   (xdoc::p
    "The set of paths of a tree is closed under prefix:
     if a path is in the tree, every prefix path is in the tree too.
     Thus, in order to represent a tree (of keys),
     a set of paths must satisfy this condition.")
   (xdoc::p
    "The condition that the prefix is a true list
     is needed because @(tsee prefixp) ignores the final @(tsee cdr)s.
     Without this condition, prefixed that are not true lists
     would be required to be in the set,
     which would be impossible because the set's elements are all true lists.")
   (xdoc::p
    "A closed non-empty set of paths always contains the empty path,
     because the empty path is a prefix of every path.")
   (xdoc::p
    "The singleton set consisting of the empty path is closed."))
  (forall (path prefix)
          (b* ((paths (bip32-path-set-fix paths)))
            (implies (and (set::in path paths)
                          (true-listp prefix)
                          (prefixp prefix path))
                     (set::in prefix paths))))
  ///

  (fty::deffixequiv bip32-path-set-closedp
    :args ((paths bip32-path-setp))
    :hints (("Goal"
             :in-theory (disable bip32-path-set-closedp-necc)
             :use ((:instance bip32-path-set-closedp-necc
                    (paths (bip32-path-set-fix paths))
                    (path (mv-nth 0 (bip32-path-set-closedp-witness paths)))
                    (prefix (mv-nth 1 (bip32-path-set-closedp-witness paths))))
                   (:instance bip32-path-set-closedp-necc
                    (path (mv-nth 0 (bip32-path-set-closedp-witness
                                     (bip32-path-set-fix paths))))
                    (prefix (mv-nth 1 (bip32-path-set-closedp-witness
                                       (bip32-path-set-fix paths)))))))))

  (defrule empty-path-in-closed-nonempty-bip32-path-set
    (implies (and (bip32-path-setp paths)
                  (not (set::empty paths))
                  (bip32-path-set-closedp paths))
             (set::in nil paths))
    :use (:instance bip32-path-set-closedp-necc
          (prefix nil)
          (path (set::head paths))))

  (defrule bip32-path-set-closedp-of-singleton-empty-path
    (bip32-path-set-closedp '(nil))
    :enable set::in)

  (in-theory (disable (:e bip32-path-set-closedp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-index-tree
  :short "Index trees underlying key trees."
  :long
  (xdoc::topapp
   (xdoc::p
    "As defined later, a key tree includes a tree of indices,
     represented as a closed non-empty set of paths."))

  (define bip32-index-treep (x)
    :returns (yes/no booleanp)
    :parents (bip32-index-tree)
    :short "Recognizer for @(tsee bip32-index-tree)."
    (and (bip32-path-setp x)
         (not (set::empty x))
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

  (define bip32-index-tree-fix ((x bip32-index-treep))
    :returns (fixed-x bip32-index-treep)
    :parents (bip32-index-tree)
    :short "Fixer for @(tsee bip32-index-tree)."
    (mbe :logic (if (bip32-index-treep x) x (list nil))
         :exec x)
    :no-function t
    ///

    (defrule bip32-index-tree-fix-when-bip32-index-treep
      (implies (bip32-index-treep x)
               (equal (bip32-index-tree-fix x)
                      x)))

    (in-theory (disable (:e bip32-index-tree-fix))))

  (fty::deffixtype bip32-index-tree
    :pred bip32-index-treep
    :fix bip32-index-tree-fix
    :equiv bip32-index-tree-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip32-valid-keys-p ((root bip32-ext-key-p) (tree bip32-index-treep))
  :returns (yes/no booleanp)
  :short "Check if all the derived keys in a tree are valid."
  :long
  (xdoc::topapp
   (xdoc::p
    "Given a root key, every path in a tree must correspond to a valid key.
     That is, all the key derivations along the path must be valid.")
   (xdoc::p
    "This function checks this condition.
     This function is used to define key trees later.")
   (xdoc::p
    "The singleton tree consisting of just the root
     (represented as the singleton set consisting of the empty path)
     trivially satisfies this key validity condition."))
  (forall (path)
          (b* ((tree (bip32-index-tree-fix tree)))
            (implies (set::in path tree)
                     (not (mv-nth 0 (bip32-ckd* root path))))))
  ///

  (fty::deffixequiv bip32-valid-keys-p
    :args ((root bip32-ext-key-p) (tree bip32-index-treep))
    :hints (("Goal"
             :in-theory (disable bip32-valid-keys-p-necc)
             :use (;; for ROOT:
                   (:instance bip32-valid-keys-p-necc
                    (root (bip32-ext-key-fix root))
                    (path (bip32-valid-keys-p-witness root tree)))
                   (:instance bip32-valid-keys-p-necc
                    (path (bip32-valid-keys-p-witness
                           (bip32-ext-key-fix root) tree)))
                   ;; for TREE:
                   (:instance bip32-valid-keys-p-necc
                    (tree (bip32-index-tree-fix tree))
                    (path (bip32-valid-keys-p-witness root tree)))
                   (:instance bip32-valid-keys-p-necc
                    (path (bip32-valid-keys-p-witness
                           root (bip32-index-tree-fix tree))))))))

  (defrule bip32-valid-keys-p-of-singleton-empty-path
    (bip32-valid-keys-p root '(nil))
    :enable (bip32-valid-keys-p
             set::in
             bip32-ckd*
             bip32-ckd-priv*
             bip32-ckd-pub*))

  (in-theory (disable (:e bip32-valid-keys-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip32-valid-depths-p ((init bytep) (tree bip32-index-treep))
  :returns (yes/no booleanp)
  :short "Check if all the key depths in a tree are valid."
  :long
  (xdoc::topapp
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
    "The singleton tree consisting of just the root
     (represented as the singleton set consisting of the empty path),
     trivially satisfies this depth validity condition."))
  (forall (path)
          (b* ((tree (bip32-index-tree-fix tree)))
            (implies (set::in path tree)
                     (< (+ (byte-fix init) (len path))
                        256))))
  ///

  (fty::deffixequiv bip32-valid-depths-p
    :args ((init natp) (tree bip32-index-treep))
    :hints (("Goal"
             :in-theory (disable bip32-valid-depths-p-necc)
             :use (;; for INIT:
                   (:instance bip32-valid-depths-p-necc
                    (init (nfix init))
                    (path (bip32-valid-depths-p-witness init tree)))
                   (:instance bip32-valid-depths-p-necc
                    (path (bip32-valid-depths-p-witness (nfix init) tree)))
                   ;; for TREE:
                   (:instance bip32-valid-depths-p-necc
                    (tree (bip32-index-tree-fix tree))
                    (path (bip32-valid-depths-p-witness init tree)))
                   (:instance bip32-valid-depths-p-necc
                    (path (bip32-valid-depths-p-witness
                           init (bip32-index-tree-fix tree))))))))

  (defrule bip32-valid-depths-p-of-singleton-empty-path
    (bip32-valid-depths-p init '(nil))
    :enable (bip32-valid-depths-p set::in))

  (in-theory (disable (:e bip32-valid-depths-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bip32-key-tree
  :short "Key trees."
  :long
  "<p>
   In a key tree, each node is labeled by a key derived from the root key.
   Thus, at the specification level, it suffices to have
   the root key and the underlying index tree,
   since all the non-root keys can be derived.
   We require each non-root key to be valid,
   as defined by @(tsee bip32-valid-keys-p).
   </p>
   <p>
   In addition to a root key and an index tree,
   our formalization of root keys includes a few other components.
   These are needed in order for the keys in the tree to be serializable
   in the manner specified in [BIP32].
   </p>
   <p>
   One of these components is the depth of the root key
   with respect to the (super)tree rooted at the master key.
   This is 0 if this tree is rooted at the master key.
   We require each key in this (sub)tree to have a depth below 256,
   taking into account the depth of the root.
   We pass the root depth to @(tsee bip32-valid-depths-p)
   to check this condition.
   </p>
   <p>
   Another component is the index of the root of this tree
   within the (super)tree rooted at the master key.
   This must be 0 if this tree's root is master key.
   Otherwise, the root of this subtree is some child within the supertree,
   and this component is the index of that child.
   Without this component,
   we would be unable to serialize the root of this subtree.
   Note that the non-root nodes in the tree have known indices.
   </p>
   <p>
   Yet another component is the fingerprint (consisting of 4 bytes [BIP32])
   of the parent of the key at the root of this tree.
   This must consist of four zeros if this root key is the master key.
   Without this component,
   we would be unable to serialize the root of this subtree.
   Note that the non-root nodes in the tree have parent fingerprints
   that can be calculated from their parent key.
   </p>"
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

(define bip32-key-identifier ((key bip32-ext-key-p))
  :returns (id byte-listp)
  :short "Identifier of an extended key."
  :long
  (xdoc::topapp
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
  ///

  (more-returns
   (id (equal (len id) 20) :name len-of-bip32-key-identifier)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-key-fingerprint ((key bip32-ext-key-p))
  :returns (fp byte-listp)
  :short "Fingerprint of an extended key."
  :long
  (xdoc::topapp
   (xdoc::p
    "The section `Key identifiers' of [BIP32]
     says that the first 32 bits (i.e. 4 bytes) of a key identifier
     are the key fingerprint."))
  (take 4 (bip32-key-identifier key))
  ///

  (more-returns
   (fp (equal (len fp) 4) :name len-of-bip32-key-fingerprint)))
