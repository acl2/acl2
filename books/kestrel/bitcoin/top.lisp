; Bitcoin Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

; the order of the following INCLUDE-BOOKs determines
; the order of the subtopics of the BITCOIN topic below:
(include-book "bytes")
(include-book "crypto")
(include-book "base58")
(include-book "base58check")
(include-book "bip32")
(include-book "bip32-executable")
(include-book "bip39")
(include-book "bip43")
(include-book "bip44")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bitcoin
  :parents (acl2::kestrel-books acl2::projects)
  :short "A library for Bitcoin."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently this library contains a formal model of some aspects of
     <a href=\"https://bitcoin.org\">Bitcoin</a>.
     It is expected that this library will be extended with more
     Bitcoin-related formalizations and tools.")
   (xdoc::p
    "This library is based on the following sources:")
   (xdoc::ul
    (xdoc::li
     "The <a href=\"https://bitcoin.org\">Bitcoin web site</a>,
      referenced as `[Site]' in the documentation of this library.")
    (xdoc::li
     "The <a href=\"https://en.bitcoin.it\">Bitcoin Wiki</a>,
      referenced as `[Wiki]' in the documentation of this library.")
    (xdoc::li
     "The <a href=\"https://github.com/bitcoin/bips\"
      >Bitcoin Improvement Proposals (BIPs) repository</a>,
      particularly the @('.mediawiki') files.
      In the documentation of this library,
      we reference individual BIPs as `[BIP<i>n</i>]',
      where <i>n</i> is the number of the BIP.")
    (xdoc::li
     "The <a href=\"https://bitcoin.org/bitcoin.pdf\">Bitcoin White Paper</a>,
      referenced as `[WP]' in the documentation of this library.")
    (xdoc::li
     "The <a href=\"https://github.com/bitcoinbook/bitcoinbook\">`Mastering
      Bitcoin' book</a>,
      referenced as `[MB]' in the documentation of this library.")))
  :order-subtopics t)
