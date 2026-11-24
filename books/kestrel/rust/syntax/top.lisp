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
(include-book "token-tree-builder")
(include-book "input-format")
(include-book "source-units")
(include-book "differential-testing")

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
     the lexical grammar, lexer, and tokenizer cover
     whitespace, comments,
     identifiers (ASCII-only for now), keywords, lifetimes,
     integer and float literals,
     character, byte, and string literals of all kinds
     (including raw strings and C strings),
     punctuation, and delimiters,
     in the editions 2021 and 2024.
     The lexer and the tokenizer are tested against rustc
     (see @(see differential-testing)),
     and @(see related-lexer-descriptions) relates our grammar
     to other descriptions of Rust's lexical structure.
     Still to come are
     Unicode identifiers and their normalization.
     The token-tree builder groups the tokens into token trees,
     by matching delimiters;
     it is proved to invert the flattening of well-formed token trees.
     The input format covers what precedes lexing
     (UTF-8 decoding, the byte order mark,
     CRLF normalization, a leading shebang),
     from the bytes of a source file,
     which it is proved to keep in full.
     A source unit holds the text of a file
     with all its lexemes, whitespace and comments included;
     the spans of tokens are offsets into that text,
     and every source unit that is made is checked
     to give back its text from its lexemes.
     Parsing and printing are future work."))
  :order-subtopics t)
