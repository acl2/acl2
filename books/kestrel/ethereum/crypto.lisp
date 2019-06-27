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
     Our Ethereum model uses cryptographic functions
     from external libraries.")
   (xdoc::p
    "In particular, the function "
    (xdoc::seeurl "crypto::keccak-256-interface" "@('keccak-256-bytes')")
    " corresponds to @($\\mathtt{KEC}$) [YP:3].")))
