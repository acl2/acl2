; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "projects/abnf/grammar-definer/defgrammar" :dir :system)
(include-book "projects/abnf/tree-operations/deftreeops" :dir :system)
(include-book "projects/abnf/grammar-operations/in-terminal-set" :dir :system)
(include-book "kestrel/utilities/integers-from-to-as-set" :dir :system)

; (depends-on "grammar/lexical-grammar.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar
  :parents (syntax-for-tools)
  :short "ABNF grammars of Rust."
  :long
  (xdoc::topstring
   (xdoc::p
    "Rust has no normative grammar.
     We write our own ABNF grammars,
     synthesized from the "
    (xdoc::ahref "https://doc.rust-lang.org/1.87.0/reference/"
                 "Rust Reference")
    ", the "
    (xdoc::ahref "https://rust-lang.github.io/fls/"
                 "Ferrocene Language Specification")
    ", and the behavior of "
    (xdoc::ahref "https://github.com/rust-lang/rust/tree/1.87.0"
                 "rustc")
    " (pinned at version 1.87.0),
     as a pivot artifact:
     documentation, cross-check target, and change-review anchor
     for the lexer and parser.")
   (xdoc::p
    "There are separate lexical and syntactic grammars
     (the latter is in development).
     Constraints that ABNF cannot express are
     labeled side conditions @('[SCn]') in the grammar files,
     each with a declarative specification in
     @(see extra-grammatical-restrictions).")
   (xdoc::p
    "We use our "
    (xdoc::seetopic "abnf::grammar-parser" "verified ABNF grammar parser")
    " to parse the grammar files into ACL2 representations.
     Since @(tsee abnf::defgrammar) does not currently provide
     an option to import the standard ABNF core rules,
     the grammar files are self-contained,
     defining their own character-class rules
     via numeric value notation."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::defgrammar *lexical-grammar*
  :short "The parsed lexical grammar of Rust (first slice)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first slice covers whitespace, comments
     (except block doc comments),
     ASCII identifiers, integer literals,
     punctuation, and delimiters;
     see the comments in @('grammar/lexical-grammar.abnf')
     for the precise scope and the side condition index.")
   (xdoc::p
    "We prove that the grammar is "
    (xdoc::seetopic "abnf::well-formedness" "well-formed")
    ", is "
    (xdoc::seetopic "abnf::closure" "closed")
    ", and only "
    (xdoc::seetopic "abnf::in-terminal-set" "generates terminals")
    " that are Unicode scalar values,
     i.e. code points excluding the surrogate range,
     as represented by the natural numbers in
     @('#x0-#xD7FF') union @('#xE000-#x10FFFF').
     The input to the grammar is assumed to be
     a sequence of code point integers;
     decoding UTF-8 bytes into code points
     is outside the scope of the grammar."))
  :file "grammar/lexical-grammar.abnf"
  :untranslate t
  :well-formed t
  :closed t

  ///

  (defruled unicode-scalar-values-only-*lexical-grammar*
    (abnf::rulelist-in-termset-p
     *lexical-grammar*
     (set::union (acl2::integers-from-to 0 #xD7FF)
                 (acl2::integers-from-to #xE000 #x10FFFF)))
    :enable (abnf::rule-in-termset-p
             abnf::repetition-in-termset-p
             abnf::element-in-termset-p
             abnf::num-val-in-termset-p
             abnf::char-val-in-termset-p
             abnf::char-insensitive-in-termset-p
             abnf::char-sensitive-in-termset-p
             set::list-in-of-union-2-left
             set::list-in-of-union-2-right)
    :disable ((:e acl2::integers-from-to)
              (:e set::union))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::deftreeops *lexical-grammar* :prefix cst)
