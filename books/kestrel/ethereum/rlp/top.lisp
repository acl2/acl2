; Ethereum Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "big-endian")
(include-book "trees")
(include-book "encoding")
(include-book "decodability")
(include-book "decoding-declarative")
(include-book "decoding-executable")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rlp
  :parents (ethereum)
  :short "Recursive Length Prefix (RLP)."
  :long
  (xdoc::topstring-p
   "RLP is a serialization (encoding) method for Ethereum,
    described in the "
   (xdoc::ahref
    "https://ethereum.org/developers/docs/data-structures-and-encoding/rlp/"
    "`Recursive-length prefix (RLP) serialization' page of [Doc]")
   ", which we reference as `[Doc:RLP]'.
    A more formal description of RLP is in [YP:B].
    An earlier reference is the page `RLP' of [Wiki],
    which we reference as `[Wiki:RLP]';
    but see @(see ethereum) about [Wiki].")
  :order-subtopics (big-endian
                    trees
                    encoding
                    decodability
                    decoding-declarative
                    decoding-executable))
