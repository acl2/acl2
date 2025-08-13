; Ethereum Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

; the order of the following INCLUDE-BOOKs determines
; the order of the subtopics of the RLP topic below:
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
    described in [YP:B] and in Page `RLP' of [Wiki];
    we reference that page of [Wiki] as `[Wiki:RLP]').")
  :order-subtopics t)
