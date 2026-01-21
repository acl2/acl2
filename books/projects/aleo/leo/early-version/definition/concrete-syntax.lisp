; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "concrete-syntax-trees")
(include-book "grammar")
(include-book "lexing-and-parsing")
(include-book "keywords")
(include-book "symbols")
(include-book "lexer")
(include-book "tokenizer")
(include-book "parser")
(include-book "parser-interface")
(include-book "pretty-printer")
(include-book "input-parser")
(include-book "input-pretty-printer")
(include-book "output-parser")
(include-book "output-pretty-printer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ concrete-syntax
  :parents (definition)
  :short "Concrete syntax of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "The concrete syntax of Leo defines
     which Unicode character sequences
     form syntactically valid Leo code and related artifacts,
     and how such sequences are organized into constructs.")
   (xdoc::p
    "The concrete syntax of Leo is formalized via ABNF grammar rules,
     complemented by a declarative specification of lexing and parsing
     that uses and disambiguates the grammar rules."))
  :order-subtopics (unicode-characters
                    concrete-syntax-trees
                    grammar
                    lexing-and-parsing
                    keywords
                    symbols
                    lexer
                    parser
                    parser-interface
                    pretty-printer))
