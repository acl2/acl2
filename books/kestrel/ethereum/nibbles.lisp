; Ethereum Library -- Nibbles
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/utilities/fixbytes/ubyte4-list" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc nibbles
  :parents (basics)
  :short "Modeling of nibbles."
  :long
  (xdoc::topp
   "[YP:C] describes @($\\mathbb{Y}$) as the set of nibbles,
    which consist of 4 bits.
    We use the library type @(tsee ubyte4) of unsigned 4-bit bytes
    to model nibbles in our Ethereum model."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc nibble-arrays
  :parents (basics)
  :short "Modeling of nibble arrays."
  :long
  (xdoc::topp
   "[YP] does not use any specific symbol for nibble arrays
    (unlike for byte arrays),
    but nibble arrays are used in [YP],
    e.g. @($y$) [YP:(190), YP:(191)] turns map keys as byte arrays
    into map keys as nibble arrays.
    Given our modeling of @(see nibbles),
    we use the library type @(tsee ubyte4-list) of
    true lists of unsigned 4-bit bytes
    to model nibble arrays in our Ethereum model,
    analogously to our model of
    <see topic='@(url byte-arrays)'>byte arrays</see>."))
