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
(include-book "verification")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-parser
  :parents (abnf)
  :short "A verified executable parser of ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "It may be possible to derive this parser from @(tsee parse-grammar*)
     (or a variant of it that resolves the ambiguity discussed there)
     via transformational refinements,
     but here we write an implementation directly
     and we prove its correctness.")
   (xdoc::p
    "The implementation and verification techniques employed for this parser
     seem more general than the parser.
     They should be applicable to parsers of other languages specified in ABNF,
     e.g. to HTTP parsers.
     It may also be possible to build a parser generator
     that turns ABNF grammars
     (satisfying certain restrictions, as with typical parser generators)
     into verified executable parsers,
     i.e. executable parsers accompanied by proofs of correctness."))
  :order-subtopics t)
