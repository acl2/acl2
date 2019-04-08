; Ethereum -- Nibbles
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/fty/defbytelist" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc nibbles
  :parents (basics)
  :short "Nibbles."
  :long
  (xdoc::topstring-p
   "[YP:C] describes @($\\mathbb{Y}$) as the set of nibbles,
    which consist of 4 bits."))

(fty::defbyte nibble
  :size 4
  :pred nibblep
  :parents (nibbles)
  :short "Fixtype of nibbles.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc nibble-arrays
  :parents (basics)
  :short "Nibble arrays."
  :long
  (xdoc::topstring-p
   "[YP] does not use any specific symbol for nibble arrays
    (unlike for byte arrays),
    but nibble arrays are used in [YP],
    e.g. @($y$) [YP:(190), YP:(191)] turns map keys as byte arrays
    into map keys as nibble arrays.
    We use true lists of @(see nibbles)
    to model nibble arrays in our Ethereum model,
    analogously to our model of
    <see topic='@(url byte-arrays)'>byte arrays</see>."))

(fty::defbytelist nibble-list
  :elt-type nibble
  :pred nibble-listp
  :parents (nibble-arrays)
  :short "Fixtype of nibble arrays.")

(defsection nibble-list-fix-ext
  :extension nibble-list-fix

  (defrule nibble-list-fix-of-rcons
    (equal (nibble-list-fix (rcons nibble nibbles))
           (rcons (nibble-fix nibble) (nibble-list-fix nibbles)))
    :enable rcons))
