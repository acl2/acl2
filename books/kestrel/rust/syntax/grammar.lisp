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
     ASCII identifiers, lifetimes, integer literals,
     character, byte, string, byte-string, and C-string literals
     (including their raw forms),
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This topic is the single list of the differences between
; the Reference and rustc that affect the grammar:
; a newly found difference should be added here,
; and described only briefly at its place in the grammar.

(defxdoc+ reference-vs-rustc
  :parents (grammar)
  :short "Where the Rust Reference and rustc differ on lexical structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our lexical grammar is synthesized from the Rust Reference
     and from the behavior of rustc, both at version 1.87.0
     (see @(see grammar)).
     In the cases listed here, the two differ
     on which inputs lex, or on how an input divides into tokens.
     In each case we follow rustc,
     since the lexer is meant to accept
     exactly the inputs that rustc's lexer accepts.")
   (xdoc::desc
    "A lone underscore right after a character or string literal"
    (xdoc::p
     "In the Reference, a "
     (xdoc::ahref
      "https://doc.rust-lang.org/1.87.0/reference/tokens.html#suffixes"
      "suffix")
     " has the form of an identifier or keyword,
      which a lone underscore is not;
      so @('\"a\"_') would be a string literal
      followed by the token @('_').
      rustc reads the underscore as the suffix of the literal,
      and rejects it.
      We reject it, by the side condition [SC11]
      (see @(tsee lexeme-cst-literal-underscore-okp))."))
   (xdoc::desc
    "The lifetime @('\\'r') immediately followed by @('#')"
    (xdoc::p
     "In the Reference, a non-raw lifetime immediately followed by @('#')
      is a "
     (xdoc::ahref
      "https://doc.rust-lang.org/1.87.0/reference/tokens.html#reserved-prefixes"
      "reserved prefix")
     ", except for the lifetime @('\\'r');
      so @('\\'r#1') would be the three tokens
      @('\\'r'), @('#'), and @('1').
      rustc rejects @('\\'r#') wherever no raw lifetime starts,
      as in @('\\'r#1').
      We reject it, by the part of the side condition [SC8]
      about lifetimes
      (see @(tsee lexeme-cst-reserved-prefix-okp))."))
   (xdoc::desc
    "An underscore at the start of the suffix of an integer literal"
    (xdoc::p
     "In the Reference, the suffix of an "
     (xdoc::ahref
      "https://doc.rust-lang.org/1.87.0/reference/tokens.html#integer-literals"
      "integer literal")
     " is any suffix that does not begin with @('e') or @('E'),
      so it may begin with an underscore.
      Since the digits of the literal may end with underscores,
      @('1_a') can then be read in two ways,
      and @('1_e') is the integer literal @('1') with suffix @('_e').
      In rustc, the digits take every underscore that follows them,
      so a suffix never begins with one;
      rustc reads @('1_e') as a float literal
      whose exponent has no digits, and rejects it.
      Our rule @('suffix-no-e') does not begin with an underscore."))
   (xdoc::desc
    "A carriage return in a string continuation"
    (xdoc::p
     "The Reference's lexical rules for "
     (xdoc::ahref
      "https://doc.rust-lang.org/1.87.0/reference/tokens.html#string-literals"
      "string literals")
     " show a string continuation as a backslash before a line feed,
      and exclude the carriage return from the characters of a string
      (other than a carriage return before a line feed,
      which is removed before lexing).
      But the accompanying text allows a carriage return
      as part of a string continuation,
      and the Reference's definition of the "
     (xdoc::ahref
      "https://doc.rust-lang.org/1.87.0/reference/expressions/literal-expr.html#string-continuation-escapes"
      "string continuation escape")
     " includes all the tabs, line feeds, carriage returns, and spaces
      that follow the line feed.
      rustc accepts a carriage return there,
      and skips that whole run of characters
      when it evaluates the literal.
      Our rule @('string-continue') includes the run,
      and the side condition [SC13] says that it includes all of it
      (see @(tsee lexeme-cst-string-continues-okp)).
      The same holds for byte string literals and C string literals."))
   (xdoc::desc
    "Zero width joiners in identifiers"
    (xdoc::p
     "The Reference says that "
     (xdoc::ahref
      "https://doc.rust-lang.org/1.87.0/reference/identifiers.html"
      "identifiers")
     " must not contain
      the zero width non-joiner (U+200C) or the zero width joiner (U+200D).
      rustc accepts both after the first character of an identifier,
      like every other character
      with the Unicode property @('XID_Continue'),
      and only warns about them
      (with its lint @('uncommon_codepoints')).
      Our identifiers are ASCII-only for now [SC4];
      when they cover Unicode,
      they will include these two characters, as in rustc."))
   (xdoc::desc
    "A lifetime immediately followed by a single quote"
    (xdoc::p
     "The Reference's rules for "
     (xdoc::ahref
      "https://doc.rust-lang.org/1.87.0/reference/tokens.html#lifetimes-and-loop-labels"
      "lifetime tokens")
     " carry the condition
      &ldquo;not immediately followed by @('\\'')&rdquo;.
      Read as a condition on which texts are lifetime tokens,
      it would make @('\\'ab\\' \\'') lex as
      the lifetime @('\\'a') followed by the byte literal @('b\\' \\''),
      since lexing takes the longest token at each point.
      rustc reads @('\\'ab\\'') as
      a character literal with two characters,
      and rejects the input.
      We reject it, by the side condition [SC12]
      (see @(tsee lexeme-cst-lifetime-quote-okp))."))))
