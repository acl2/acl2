; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "positions")
(include-book "spans")
(include-book "unicode-characters")
(include-book "unicode-xid")
(include-book "keywords")
(include-book "tokens")
(include-book "token-trees")
(include-book "token-tree-operations")
(include-book "grammar")
(include-book "extra-grammatical-restrictions")
(include-book "lexer")
(include-book "tokenizer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ syntax-for-tools
  :parents (rust::rust)
  :short "An ACL2 representation of Rust concrete syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "This directory provides the tool-oriented syntax track
     of the Rust library, in the @('\"RUST$\"') package:
     lexing (including token trees, the currency of macro expansion),
     parsing, and printing of Rust source code,
     aiming at the full surface language.
     The language formalization track,
     in the @('\"RUST\"') package (see @(see rust::rust)),
     gives semantics to defined subsets.
     This two-track organization, and the @('$') package-name convention,
     follow the C library (see @(see c$::syntax-for-tools)).")
   (xdoc::p
    "This is work in progress.
     At this time of writing,
     the lexical grammar covers a first slice
     of Rust's lexical structure,
     and the lexer and tokenizer are done for that slice.
     Token trees have their representation,
     well-formedness, and flattening,
     but not yet the builder that groups tokens into trees.
     Parsing and printing are future work."))
  :order-subtopics t)
