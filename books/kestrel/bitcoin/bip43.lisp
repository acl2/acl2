; Bitcoin Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "bip32")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bip43
  :parents (bitcoin)
  :short "Bitcoin Improvement Proposal (BIP) 43."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is described at
     <a href=\"https://github.com/bitcoin/bips/blob/master/bip-0043.mediawiki\"
     >this page in the @('bitcoin/bips') repository on GitHub</a>,
     linked from
     <a href=\"https://en.bitcoin.it/wiki/BIP_0043\"
     >Page `BIP 0043' of [Wiki]</a>.
     We refer to the document at the first URL as `[BIP43]'
     in the documentation below."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip43-purpose
  :short "Purposes."
  :long
  (xdoc::topstring
   (xdoc::p
    "[BIP43] recommends to index of the first level of a BIP 32 key tree
     as an indication of ``purpose''.
     We introduce a fixtype for the possible values of this index.")
   (xdoc::p
    "[BIP43] uses an apostrophe to indicate that
     the purpose key should be hardened.
     Therefore, the purpose number should be below @($2^{31}$),
     so that it can be increased by that amount
     to indicate a hardened key.")
   (xdoc::p
    "[BIP43] also states that number 0 is already taken by BIP 32
     to indicate a default account.
     Thus, it seems reasonable to exclude 0 from
     the set of acceptable purpose numbers."))

  (define bip43-purposep (x)
    :returns (yes/no booleanp)
    :parents (bip43-purpose)
    :short "Recognizer for @(tsee bip43-purpose)."
    (integer-range-p 1 (expt 2 31) x)
    :no-function t)

  (std::deffixer bip43-purpose-fix
    :pred bip43-purposep
    :body-fix 1
    :parents (bip43-purpose)
    :short "Fixer for @(tsee bip43-purpose).")

  (fty::deffixtype bip43-purpose
    :pred bip43-purposep
    :fix bip43-purpose-fix
    :equiv bip43-purpose-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip43-key-tree-has-purpose-p ((tree bip32-key-treep)
                                      (purpose bip43-purposep))
  :returns (yes/no booleanp)
  :short "Check if a key tree includes a subtree for a given purpose."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check if the tree is rooted at the private master key
     and includes the singleton path with the (hardened) purpose number."))
  (and (bip32-key-tree-priv-p tree)
       (equal (bip32-key-tree->root-depth tree) 0)
       (b* ((purpose-hardened (+ (bip43-purpose-fix purpose) (expt 2 31))))
         (bip32-path-in-tree-p (list purpose-hardened) tree)))
  :no-function t
  :guard-hints (("Goal" :in-theory (enable bip43-purposep ubyte32p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip43-export-key ((tree bip32-key-treep)
                          (path ubyte32-listp)
                          (public? booleanp))
  :guard (and (bip32-path-in-tree-p path tree)
              (or public? (bip32-key-tree-priv-p tree)))
  :returns (exported byte-listp)
  :short "BIP 43 key export."
  :long
  (xdoc::topstring
   (xdoc::p
    "[BIP43] prescribes that BIP 32 key serialization be always done
     with the version numbers of the mainnet,
     i.e. @(tsee *bip32-version-priv-main*)
     and @(tsee *bip32-version-pub-main*).")
   (xdoc::p
    "This function specializes @(tsee bip32-export-key)
     by eliminating the boolean argument that selects mainnet or testnet,
     and by passing @('t') as its value to @(tsee bip32-export-key)."))
  (bip32-export-key tree path t public?)
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip43-import-key ((bytes byte-listp))
  :returns (mv (error? booleanp)
               (tree bip32-key-treep))
  :short "BIP 43 key import."
  :long
  (xdoc::topstring
   (xdoc::p
    "[BIP43] prescribes that BIP 32 key serialization be always done
     with the version numbers of the mainnet,
     i.e. @(tsee *bip32-version-priv-main*)
     and @(tsee *bip32-version-pub-main*).")
   (xdoc::p
    "This function calls @(tsee bip32-import-key)
     and ensures that the serialized key was for the mainnet."))
  (b* (((mv error? tree mainnet?) (bip32-import-key bytes))
       ((when error?) (mv t tree))
       ((unless mainnet?) (mv t tree)))
    (mv nil tree))
  :no-function t
  :hooks (:fix))
