; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

;; The topics under concrete-syntax have both concrete-syntax
;; and parsing-and-printing as parents.
(include-book "concrete-syntax")

(include-book "syntax-abstraction")
(include-book "parser-interface")
(include-book "printer")
(include-book "parse-directory-files") ; for testing
(include-book "value-printing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parsing-and-printing
  :parents (remora)
  :short "Parsing and Printing Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parsing in the broad sense includes reading source code from
     strings, files, or channels; input decoding;
     construction of concrete syntax trees (CSTs) following grammar rules;
     extra-grammatical constraint checks; and syntax abstraction
     from CSTs to abstract syntax trees (ASTs).")
   (xdoc::p
    "Some of these topics are covered under @(tsee concrete-syntax).
     Here we provide more detail broadly on parsing and printing.")
   (xdoc::p
    "The " (xdoc::seetopic "grammar" "ABNF grammar") " is defined
     on an input sequence of Unicode characters (as code point scalar values).
     Reading source code and conversion from input bytes in UTF-8 to
     a list of codepoints is handled by "
     (xdoc::seetopic "parser-interface" "parser interface")
     " functions such as @(tsee parse-from-string) and
     @(tsee parse-from-file).")
   (xdoc::p
    "The core @(tsee parser) does parsing in the narrow sense:
     it applies the grammar rules to a list of Unicode characters
     and returns @(tsee concrete-syntax-trees) (CSTs).
     The CSTs record all the grammar rules
     used, including those for whitespace and comments,
     and are fully annotated with the Unicode characters
     matching the rules used.")
   (xdoc::p
    "After the core parser has run, the CSTs are checked for
     extra-grammatical constraints: constraints on the syntax
     that cannot be expressed or that are difficult to express
     in ABNF.  This is handled in @(tsee post-parsing).")
   (xdoc::p
    "Finally, CSTs are lifted to "
    (xdoc::seetopic "abstract-syntax-trees" "ASTs") " by "
    (xdoc::seetopic "syntax-abstraction" "syntax abstraction")
    ".")
   (xdoc::p
    "We define a "
    (xdoc::seetopic "printer" "pretty printer")
    " that takes an AST and outputs Remora source code.")
   (xdoc::p
    "For testing parsing and printing, we have defined functions
     for parsing all the files in a given directory, and for
     parsing, printing, reparsing, and comparing the two ASTs.
     See @(tsee parse-directory-utilities)."))

  :order-subtopics (concrete-syntax
                    grammar
                    parser-interface
                    parser
                    concrete-syntax-trees
                    post-parsing
                    syntax-abstraction
                    printer
                    parse-directory-utilities
                    value-printing))
