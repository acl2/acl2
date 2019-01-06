; Ethereum Library -- RLP (Recursive Length Prefix)
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

; the order of the following INCLUDE-BOOKs determines
; the order of the subtopics of the ETHEREUM topic below:
(include-book "big-endian")
(include-book "trees")
(include-book "encoding")
(include-book "decodability")
(include-book "decoding-declarative")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rlp
  :parents (ethereum)
  :short "Recursive Length Prefix (RLP)."
  :long
  (xdoc::topp
   "RLP is a serialization (encoding) method for Ethereum,
    described in [YP:B] and in
    <a href=\"https://github.com/ethereum/wiki/wiki/RLP\">Page `RLP'
    of [Wiki]</a>;
    we reference that page of [Wiki] as `[Wiki:RLP]').")
  :order-subtopics t)
