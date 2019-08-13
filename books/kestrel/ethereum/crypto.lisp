; Ethereum Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc cryptography
  :parents (ethereum)
  :short "Cryptography in Ethereum."
  :long
  (xdoc::topstring
   (xdoc::p
    "Ethereum uses a number of cryptographic functions
     that are described in external standards.
     Our Ethereum model uses cryptographic functions from "
    (xdoc::seeurl "crypto::cryptography" "external libraries")
    ".")
   (xdoc::p
    "Our current Ethereum model uses the following cryptographic functions:")
   (xdoc::ul
    (xdoc::li
     (xdoc::seeurl "crypto::keccak-256-interface" "@('keccak-256-bytes')")
     ", which corresponds to @($\\mathtt{KEC}$) [YP:3].")
    (xdoc::li
     "@(tsee secp256k1-priv-to-pub),
      which corresponds to @($\\mathtt{ECDSAPUBKEY}$) [YP:F]
      (modulo a different but isomorphic data representation,
      namely byte arrays for the former,
      and @(tsee ecurve::secp256k1-priv-key)
      and @(tsee ecurve::secp256k1-pub-key) values for the latter.")
    (xdoc::li
     "@(tsee secp256k1-sign-det-rec),
      which corresponds to @($\\mathtt{ECDSASIGN}$) [YP:F]
      in essence, but see @(tsee make-signed-transaction) for details."))))
