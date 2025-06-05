; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "grammar")
(include-book "lexer")
(include-book "tokenizer")
(include-book "parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ concrete-syntax
  :parents (pfcs)
  :short "Concrete syntax of PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a concrete syntax of PFCSes
     to ease reading and writing them.
     We define the syntax via an ABNF grammar,
     which we plan to complete with a declarative specification
     of parsing of PFCSes according to the grammar.
     We define an executable lexer, tokenizer, and parser to CSTs
     (concrete syntax trees).")))
