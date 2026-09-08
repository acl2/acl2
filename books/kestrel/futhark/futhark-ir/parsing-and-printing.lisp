; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "concrete-syntax")
(include-book "syntax-abstraction")
(include-book "parser-interface")
(include-book "printer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parsing-and-printing
  :parents (futhark-ir)
  :short "Parsing and printing Futhark IR."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parsing in the broad sense includes input decoding, construction of
     concrete syntax trees (CSTs) according to the ABNF grammar, checks for
     token-level side conditions, and syntax abstraction from CSTs to the
     FTY abstract syntax.")
   (xdoc::p
    "The grammar and core parser operate on lists of Unicode code points,
     represented as natural numbers.  The public string entry point
     @(tsee parse-ir-from-string) treats ACL2 strings as UTF-8 byte
     strings, decodes them to code points, and then calls the core parser.
     This follows the convention used by the Remora front end.")
   (xdoc::p
    "The core parser produces ABNF CSTs that preserve the grammar structure,
     including whitespace and comments.  @(see syntax-abstraction) maps those
     CSTs to the Futhark IR ASTs and enforces side conditions such as the
     distinction between words, names, keywords, and literal-looking words.")
   (xdoc::p
    "The printer maps the AST representation back to textual Futhark IR as an
     ACL2 string.  The main round-trip entry points are
     @(tsee parse-ir-from-string) and @(tsee print-fut-program)."))
  :order-subtopics (concrete-syntax
                    ir-grammar
                    lexical-syntax
                    identifier-syntax
                    parser
                    concrete-syntax-trees
                    parser-interface
                    syntax-abstraction
                    printer))
