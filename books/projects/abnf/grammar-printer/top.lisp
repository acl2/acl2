; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "executable")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-printer
  :parents (abnf)
  :short "A pretty-printer of ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pretty-print ABNF abstract syntax to ABNF concrete syntax.
     This pretty-printer is currently not verified,
     but we may verify it in the future.")
   (xdoc::p
    "Currently this pretty-printer is only used
     by some ABNF tools in this library.")))
