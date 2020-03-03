; Bitcoin Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "bip43")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bip44
  :parents (bitcoin)
  :short "Bitcoin Improvement Proposal (BIP) 44."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is described at
     <a href=\"https://github.com/bitcoin/bips/blob/master/bip-0044.mediawiki\"
     >this page in the @('bitcoin/bips') repository on GitHub</a>,
     linked from
     <a href=\"https://en.bitcoin.it/wiki/BIP_0044\"
     >Page `BIP 0044' of [Wiki]</a>.
     We refer to the document at the first URL as `[BIP44]'
     in the documentation below."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *bip44-purpose*
  :short "Prescribed value of the purpose field."
  44
  ///
  (assert-event (bip43-purposep *bip44-purpose*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip44-compliant-depth-p ((tree bip32-key-treep))
  :returns (yes/no booleanp)
  :short "Check if the depth of a key tree
          complies with the BIP 44 wallet structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [BIP44],
     the key tree stops at depth 5,
     i.e. the address keys have no children
     (and therefore no grandchildren, great-grandchildren, etc.).
     This is formally expressed by saying that
     every path in the tree has a length below 6."))
  (forall (path)
          (implies (and (ubyte32-listp path)
                        (bip32-path-in-tree-p path tree))
                   (< (len path) 6)))
  ///

  (fty::deffixequiv-sk bip44-compliant-depth-p
    :args ((tree bip32-key-treep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip44-compliant-addresses-for-limit-p ((tree bip32-key-treep)
                                                  (coin-index ubyte32p)
                                                  (account-index ubyte32p)
                                                  (chain-index ubyte32p)
                                                  (address-index-limit natp))
  :guard (bip32-path-in-tree-p (list (+ *bip44-purpose* (expt 2 31))
                                     coin-index
                                     account-index
                                     chain-index)
                               tree)
  :returns (yes/no booleanp)
  :short "Check if the address keys under a given chain key in a tree
          comply with the BIP 44 wallet structure,
          for a given address index limit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The chain key is identified by
     a coin index, an account index, and a chain index,
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
     except for the rare cases in which there are gaps.")
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
     but no address keys under it have been created yet."))
  (forall (address-index)
          (implies (ubyte32p address-index)
                   (b* ((path (list (+ *bip44-purpose* (expt 2 31))
                                    coin-index
                                    account-index
                                    chain-index
                                    address-index)))
                     (if (< address-index (nfix address-index-limit))
                         (or (bip32-path-in-tree-p path tree)
                             (mv-nth 0 (bip32-ckd*
                                        (bip32-key-tree->root-key tree)
                                        path)))
                       (not (bip32-path-in-tree-p path tree))))))
  ///

  ;; Calling FTY::DEFFIXEQUIV-SK directly with all arguments is too slow.
  ;; So we manually split the arguments and call FTY::DEFFIXEQUIV,
  ;; since FTY::DEFFIXEQUIV-SK does not support
  ;; generating hints for only some arguments yet.
  ;; The following hints are the ones generated via FTY::DEFFIXEQUIV-SK.

  (fty::deffixequiv bip44-compliant-addresses-for-limit-p
    :args ((tree bip32-key-treep)
           (coin-index ubyte32p)
           (address-index-limit natp))
    :hints (("Goal"
             :in-theory (e/d (bip44-compliant-addresses-for-limit-p)
                             (bip44-compliant-addresses-for-limit-p-necc))
             :use
             ((:instance bip44-compliant-addresses-for-limit-p-necc
               (tree (bip32-key-tree-fix tree))
               (address-index (bip44-compliant-addresses-for-limit-p-witness
                               tree coin-index account-index
                               chain-index address-index-limit)))
              (:instance bip44-compliant-addresses-for-limit-p-necc
               (address-index (bip44-compliant-addresses-for-limit-p-witness
                               (bip32-key-tree-fix tree)
                               coin-index account-index
                               chain-index address-index-limit)))
              (:instance bip44-compliant-addresses-for-limit-p-necc
               (coin-index (ubyte32-fix coin-index))
               (address-index (bip44-compliant-addresses-for-limit-p-witness
                               tree coin-index account-index
                               chain-index address-index-limit)))
              (:instance bip44-compliant-addresses-for-limit-p-necc
               (address-index (bip44-compliant-addresses-for-limit-p-witness
                               tree (ubyte32-fix coin-index)
                               account-index
                               chain-index address-index-limit)))
              (:instance bip44-compliant-addresses-for-limit-p-necc
               (address-index-limit (nfix address-index-limit))
               (address-index (bip44-compliant-addresses-for-limit-p-witness
                               tree coin-index account-index
                               chain-index address-index-limit)))
              (:instance bip44-compliant-addresses-for-limit-p-necc
               (address-index (bip44-compliant-addresses-for-limit-p-witness
                               tree
                               coin-index account-index chain-index
                               (nfix address-index-limit))))))))

  (fty::deffixequiv bip44-compliant-addresses-for-limit-p
    :args ((account-index ubyte32p)
           (chain-index ubyte32p))
    :hints (("Goal"
             :in-theory (e/d (bip44-compliant-addresses-for-limit-p)
                             (bip44-compliant-addresses-for-limit-p-necc))
             :use
             ((:instance bip44-compliant-addresses-for-limit-p-necc
               (account-index (ubyte32-fix account-index))
               (address-index (bip44-compliant-addresses-for-limit-p-witness
                               tree coin-index account-index
                               chain-index address-index-limit)))
              (:instance bip44-compliant-addresses-for-limit-p-necc
               (address-index (bip44-compliant-addresses-for-limit-p-witness
                               tree
                               coin-index (ubyte32-fix account-index)
                               chain-index address-index-limit)))
              (:instance bip44-compliant-addresses-for-limit-p-necc
               (chain-index (ubyte32-fix chain-index))
               (address-index (bip44-compliant-addresses-for-limit-p-witness
                               tree coin-index account-index
                               chain-index address-index-limit)))
              (:instance bip44-compliant-addresses-for-limit-p-necc
               (address-index (bip44-compliant-addresses-for-limit-p-witness
                               tree coin-index
                               account-index (ubyte32-fix chain-index)
                               address-index-limit))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip44-compliant-addresses-p ((tree bip32-key-treep)
                                        (coin-index ubyte32p)
                                        (account-index ubyte32p)
                                        (chain-index ubyte32p))
  :guard (bip32-path-in-tree-p (list (+ *bip44-purpose* (expt 2 31))
                                     coin-index
                                     account-index
                                     chain-index)
                               tree)
  :returns (yes/no booleanp)
  :short "Check if the address keys under a given chain key in a tree
          comply with the BIP 44 wallet structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is obtained by existentially quantifying the address index limit
     in @(tsee bip44-compliant-addresses-for-limit-p).
     See the documentation of that function for details.")
   (xdoc::p
    "[BIP44] states that the address keys are not hardened,
     so we require the limit to be at most @($2^{31}$)."))
  (exists (address-index-limit)
          (and (natp address-index-limit)
               (<= address-index-limit (expt 2 31))
               (bip44-compliant-addresses-for-limit-p tree
                                                      coin-index
                                                      account-index
                                                      chain-index
                                                      address-index-limit)))
  ///

  (fty::deffixequiv-sk bip44-compliant-addresses-p
    :args ((tree bip32-key-treep)
           (coin-index ubyte32p)
           (account-index ubyte32p)
           (chain-index ubyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip44-compliant-chains-p ((tree bip32-key-treep)
                                     (coin-index ubyte32p)
                                     (account-index ubyte32p))
  :guard (bip32-path-in-tree-p (list (+ *bip44-purpose* (expt 2 31))
                                     coin-index
                                     account-index)
                               tree)
  :returns (yes/no booleanp)
  :short "Check if the chain keys under a given account key in a tree
          comply with the BIP 44 wallet structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee bip44-compliant-addresses-p)
     and @(tsee bip44-compliant-addresses-for-limit-p),
     but the limit is always 2 in this case,
     because there must be exactly two chains for each account:
     an external chain and a change chain.
     So we do not need the existential quantification over the limit
     and we just have a single level of (universal) quantification.")
   (xdoc::p
    "There is also another difference with address keys,
     namely that we require both chain keys to be present.
     While an invalid address key is acceptable and is simply skipped,
     we cannot skip an external or change chain for an account.
     If either chain key is invalid,
     then presumably the whole account key should be skipped;
     this is not explicitly said in [BIP44], but it seems reasonable.")
   (xdoc::p
    "Furthermore, in this predicate we require the address keys under each chain
     to be compliant with the BIP 44 structure.
     We are defining key tree compliance incrementally here."))
  (forall (chain-index)
          (implies (ubyte32p chain-index)
                   (b* ((path (list (+ *bip44-purpose* (expt 2 31))
                                    coin-index
                                    account-index
                                    chain-index)))
                     (case chain-index
                       (0 (and (bip32-path-in-tree-p path tree)
                               (bip44-compliant-addresses-p
                                tree coin-index account-index chain-index)))
                       (1 (and (bip32-path-in-tree-p path tree)
                               (bip44-compliant-addresses-p
                                tree coin-index account-index chain-index)))
                       (t (not (bip32-path-in-tree-p path tree)))))))
  ///

  (fty::deffixequiv-sk bip44-compliant-chains-p
    :args ((tree bip32-key-treep)
           (coin-index ubyte32p)
           (account-index ubyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip44-compliant-accounts-for-limit-p ((tree bip32-key-treep)
                                                 (coin-index ubyte32p)
                                                 (account-index-limit natp))
  :guard (bip32-path-in-tree-p (list (+ *bip44-purpose* (expt 2 31))
                                     coin-index)
                               tree)
  :returns (yes/no booleanp)
  :short "Check if the account keys in a tree
          comply with the BIP 44 wallet structure,
          for a given account index limit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee bip44-compliant-addresses-for-limit-p).")
   (xdoc::p
    "[BIP44] says that hardened keys are used for accounts.
     Thus, we require all non-hardened account keys to be absent
     and we apply the limit to hardened account keys
     by adding @($2^{31}$) to the limit.")
   (xdoc::p
    "For each account index below the limit,
     we require not only the account key to be present,
     but also the chain keys to be compliant to the BIP 44 wallet structure;
     again, we are defining compliance incrementally.")
   (xdoc::p
    "We allow a gap in the account keys only if
     the account key is invalid,
     or any chain key under it is invalid.
     See the discussion about this in @(tsee bip44-compliant-chains-p)."))
  (forall (account-index)
          (implies (ubyte32p account-index)
                   (b* ((root-key (bip32-key-tree->root-key tree))
                        (path (list (+ *bip44-purpose* (expt 2 31))
                                    coin-index
                                    account-index)))
                     (cond ((< account-index (expt 2 31))
                            (not (bip32-path-in-tree-p path tree)))
                           ((< account-index (+ (nfix account-index-limit)
                                                (expt 2 31)))
                            (or (and (bip32-path-in-tree-p path tree)
                                     (bip44-compliant-chains-p
                                      tree coin-index account-index))
                                (mv-nth 0 (bip32-ckd* root-key path))
                                (mv-nth 0 (bip32-ckd* root-key
                                                      (rcons 0 path)))
                                (mv-nth 0 (bip32-ckd* root-key
                                                      (rcons 1 path)))))
                           (t (not (bip32-path-in-tree-p path tree)))))))
  ///

  (local (in-theory (enable rcons)))

  (fty::deffixequiv-sk bip44-compliant-accounts-for-limit-p
    :args ((tree bip32-key-treep)
           (coin-index ubyte32p)
           (account-index-limit natp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip44-compliant-accounts-p ((tree bip32-key-treep)
                                       (coin-index ubyte32p))
  :guard (bip32-path-in-tree-p (list (+ *bip44-purpose* (expt 2 31))
                                     coin-index)
                               tree)
  :returns (yes/no booleanp)
  :short "Check if the account keys in a tree
          comply with the BIP 44 wallet structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee bip44-compliant-addresses-p)."))
  (exists (account-index-limit)
          (and (natp account-index-limit)
               (bip44-compliant-accounts-for-limit-p
                tree coin-index account-index-limit)))
  ///

  (fty::deffixequiv-sk bip44-compliant-accounts-p
    :args ((tree bip32-key-treep) (coin-index ubyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc bip44-coin-types
  :short "Coin types."
  :long
  (xdoc::topstring-p
   "According to [BIP44], these are indices in the key tree,
    for which hardened keys must be used.
    Thus, we model coin types as 31-bit unsigned bytes
    (with the understanding that they have to be increased by @($2^{31}$)
    to be used as indices in the tree)."))

(fty::defbyte bip44-coin-type
  :size 31
  :parents (bip44-coin-types)
  :short "Fixtype of coin types.")

(fty::defset bip44-coin-type-set
  :elt-type bip44-coin-type
  :elementp-of-nil nil
  :pred bip44-coin-type-setp
  :short "Osets of coin types.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip44-compliant-coins-for-set-p ((tree bip32-key-treep)
                                            (coins bip44-coin-type-setp))
  :returns (yes/no booleanp)
  :short "Check if the coin keys under the purpose key in a tree
          comply with the BIP 44 wallet structure,
          for a given set of coin types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee bip44-compliant-addresses-for-limit-p),
     but instead of an address limit we have a set of coin types.
     We require that there is a coin key in the tree
     exactly for each coin type in the given set.
     Furthermore, we require, for each such coin key,
     its children account keys
     to be compliant with the BIP 44 wallet structure.")
   (xdoc::p
    "Following [BIP44], we require each coin key to be hardened."))
  (forall (coin-index)
          (implies (ubyte32p coin-index)
                   (b* ((path (list (+ *bip44-purpose* (expt 2 31))
                                    coin-index)))
                     (cond ((< coin-index (expt 2 31))
                            (not (bip32-path-in-tree-p path tree)))
                           ((set::in (- coin-index (expt 2 31))
                                     (bip44-coin-type-set-fix coins))
                            (and (bip32-path-in-tree-p path tree)
                                 (bip44-compliant-accounts-p tree coin-index)))
                           (t (not (bip32-path-in-tree-p path tree)))))))
  ///

  (fty::deffixequiv-sk bip44-compliant-coins-for-set-p
    :args ((tree bip32-key-treep) (coins bip44-coin-type-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk bip44-compliant-coins-p ((tree bip32-key-treep))
  :returns (yes/no booleanp)
  :short "Check if the coin keys under the purpose key in a tree
          comply with the BIP 44 wallet structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee bip44-compliant-addresses-p),
     but we existentially quantify over the set of coin types.")
   (xdoc::p
    "Thus, the existential witness is
     the set of coin types supported by the key tree."))
  (exists (coins)
          (and (bip44-coin-type-setp coins)
               (bip44-compliant-coins-for-set-p tree coins)))
  :skolem-name bip44-supported-coin-types
  ///

  (defrule bip44-coin-type-setp-of-bip44-supported-coin-types
    (implies (bip44-compliant-coins-p tree)
             (bip44-coin-type-setp (bip44-supported-coin-types tree))))

  (fty::deffixequiv-sk bip44-compliant-coins-p
    :args ((tree bip32-key-treep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip44-compliant-tree-p ((tree bip32-key-treep))
  :returns (yes/no booleanp)
  :short "Check if a key tree complies with the BIP 44 wallet structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "We require the tree to start with the master private key (depth 0),
     to include the purpose key,
     to have compliant subtrees for any supported coins,
     and to not exceed depth 5."))
  (and (equal 0 (bip32-key-tree->root-depth tree))
       (bip32-key-tree-priv-p tree)
       (bip43-key-tree-has-purpose-p tree *bip44-purpose*)
       (bip44-compliant-coins-p tree)
       (bip44-compliant-depth-p tree))
  :no-function t
  :hooks (:fix))
