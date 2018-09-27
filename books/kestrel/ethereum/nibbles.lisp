; Ethereum Library -- Nibbles
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/utilities/fixbytes/ubyte4" :dir :system)

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
