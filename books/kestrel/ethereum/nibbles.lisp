; Ethereum Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/fty/nibble-list" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc nibbles
  :parents (basics)
  :short "Nibbles."
  :long
  (xdoc::topstring
   (xdoc::p
    "[YP:C] describes @($\\mathbb{Y}$) as the set of sequences of nibbles,
     i.e. half bytes.
     [YP] does not use any specific symbol for the set of nibbles
     (unlike @($\\mathbb{O}$) for the set of bytes [YP:B]).
     We use the library type @(tsee nibble) to model the set of nibbles.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection nibble-arrays
  :parents (basics)
  :short "Nibble arrays."
  :long
  (xdoc::topstring-p
   "[YP:C] describes @($\\mathbb{Y}$) as the set of sequences of nibbles.
    We use the library type @(see nibble-list) to model nibble arrays."))
