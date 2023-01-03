; JSON Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSON")

(include-book "grammar")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ concrete-syntax
  :parents (json)
  :short "Concrete syntax of JSON."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use our "
    (xdoc::seetopic "abnf::grammar-parser" "verified grammar parser")
    " to turn the ABNF grammar of JSON (from the JSON RFC)
     into a formal representation in ACL2.")
   (xdoc::p
    "As the grammar is technically ambiguous (in matters of whitespace),
     it remains to complete the formal specification
     of the concrete syntax of JSON
     with a suitable disambiguation, which we plan to do soon.")))
