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

; The versions named in this topic are the library's pins.
; When one of them moves, check again, against the new versions:
; the cases in the topic reference-vs-rustc below;
; the tests transcribed from rustc (tests/rustc-lexer-vectors.lisp);
; the Unicode tables (unicode-xid.lisp);
; and the versions and commits in the topic related-lexer-descriptions below.

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
    "The Reference and rustc are both taken at version 1.87.0,
     and the Unicode data at version 16.0.0,
     which is the version that rustc 1.87.0 uses for identifiers
     (see @(see unicode-xid)).
     The Ferrocene Language Specification, at the link above,
     follows the latest release of Rust
     (1.100.0 at this time of writing),
     so we use it as a secondary source.
     Where the Reference and rustc differ, we follow rustc
     (see @(see reference-vs-rustc)).")
   (xdoc::p
    "There are separate lexical and syntactic grammars
     (the latter is in development).
     Constraints that ABNF cannot express are
     labeled side conditions @('[SCn]') in the grammar files,
     each with a declarative specification in
     @(see extra-grammatical-restrictions).")
   (xdoc::p
    "Our grammars are generative:
     a rule says which texts have a certain form,
     and several rules, or several alternatives of one rule,
     may match texts at the start of the same input.
     Which of those texts is the next token
     is not said by the grammar but by the side conditions:
     it is a longest one [SC1], among those that
     the other side conditions allow.
     The Reference at version 1.87.0 is written in the same way,
     except that it does not say how the choice is made.
     Later versions of the Reference,
     and other descriptions of Rust's lexical structure,
     use grammars of another kind,
     in which the alternatives of a rule are tried in order
     and the first one that matches is taken
     (see @(see related-lexer-descriptions)).
     We use ABNF for two reasons.
     One is that we have a verified parser of ABNF grammars
     and operations on their parse trees,
     so the grammar in the file is
     the grammar that the theorems about the lexer refer to.
     The other is that a generative grammar with side conditions
     says which lexings are correct without saying how to find them,
     which makes it a specification to prove a lexer against.
     The price is that the choice among the matches
     needs conditions of its own,
     which a grammar with ordered alternatives expresses
     by the order.")
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
     ASCII identifiers, lifetimes, integer and float literals,
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

; This topic is the single list of the places where the Reference
; does not tell us what rustc does about lexical structure.
; A newly found one should be added here, under the heading that fits it,
; and described only briefly at its place in the grammar.

(defxdoc+ reference-vs-rustc
  :parents (grammar)
  :short "Where the Rust Reference, at version 1.87.0,
          differs from rustc on lexical structure,
          or leaves open what rustc does."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our lexical grammar is synthesized from the Rust Reference
     and from the behavior of rustc, both at version 1.87.0
     (see @(see grammar)).
     This topic lists the cases, found so far,
     in which the Reference does not tell us what rustc does.
     They are of two kinds.
     In the first, the Reference says one thing and rustc does another:
     the two differ on which inputs lex,
     or on how an input divides into tokens.
     In the second, the Reference can be read in more than one way,
     or says two things that do not agree,
     and rustc does one of them.
     In each case we follow rustc,
     since the lexer is meant to accept
     exactly the inputs that rustc's lexer accepts.")
   (xdoc::p
    "What rustc does in each case,
     we have observed by running rustc 1.87.0
     (see @(see lexer) for how we observe
     which inputs it lexes, and into how many tokens).
     What the Reference says is our reading of its rules and text.
     The Reference of that version gives a rule for each kind of token,
     but it does not say how an input divides into tokens
     where rules match texts of different lengths;
     we read it with the usual convention
     that the longest token is taken [SC1].
     The last section of this topic says
     what became of these cases in a later version of the Reference.")
   (xdoc::h3 "Where the Reference says one thing and rustc does another")
   (xdoc::desc
    "The characters @('/*') inside a block comment"
    (xdoc::p
     "The Reference says that block "
     (xdoc::ahref
      "https://doc.rust-lang.org/1.87.0/reference/comments.html"
      "comments")
     " nest, and its rule gives the content of a block comment as
      nested block comments and any other characters
      that are not the two characters @('*/').
      By that rule, @('/* a /*/') is a block comment,
      in which the second slash is one of the other characters.
      rustc takes every @('/*') inside a block comment
      as the start of a nested one,
      even where a slash follows its star.
      So in @('/* a /*/') a nested comment starts and nothing ends,
      and rustc rejects the input as an unterminated block comment.
      We reject it, by the side condition [SC2]
      (see @(tsee block-comment-string-p)).
      The same holds for block doc comments, as in @('/*!/*/'),
      which our grammar does not yet tell from other block comments."))
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
      The rule for float literals that end with a period
      carries a condition of the same form,
      and there it restricts which texts are tokens:
      in @('1..2'), the text @('1.') is not a float literal,
      and the token is the shorter @('1').
      Read in the same way, the condition on lifetimes
      makes @('\\'ab\\' \\'') lex as
      the lifetime @('\\'a') followed by the byte literal @('b\\' \\''):
      there @('\\'ab') is not a lifetime token, and @('\\'a') is one.
      rustc reads @('\\'ab\\'') as
      a character literal with two characters,
      and rejects the input.
      We reject it, by the side condition [SC12]
      (see @(tsee lexeme-cst-lifetime-quote-okp))."))
   (xdoc::h3 "Where the Reference is ambiguous or contradicts itself")
   (xdoc::desc
    "An underscore between the digits of a number literal and its suffix"
    (xdoc::p
     "In the Reference, the digits of an "
     (xdoc::ahref
      "https://doc.rust-lang.org/1.87.0/reference/tokens.html#integer-literals"
      "integer literal")
     " may end with underscores, and the "
     (xdoc::ahref
      "https://doc.rust-lang.org/1.87.0/reference/tokens.html#suffixes"
      "suffix")
     " after them may begin with one.
      So @('1_u8') can be read with suffix @('u8') or with suffix @('_u8'),
      and the same goes for a "
     (xdoc::ahref
      "https://doc.rust-lang.org/1.87.0/reference/tokens.html#floating-point-literals"
      "float literal")
     " such as @('1.5_f32').
      Likewise, @('1_e') and @('1.0_e') can be read
      as literals with suffix @('_e'),
      and also as reserved forms:
      a number followed by @('e') and no digit.
      In rustc, the digits take every underscore that follows them,
      so a suffix never begins with one:
      @('1_u8') has type @('u8'), @('1.5_f32') has type @('f32'),
      and @('1_e') and @('1.0_e') are rejected,
      as exponents without digits.
      Our rules for a suffix after digits,
      @('suffix-no-e') and @('suffix-no-underscore'),
      do not begin with an underscore."))
   (xdoc::desc
    "A hexadecimal digit at the start of the suffix of a hexadecimal literal"
    (xdoc::p
     "In the Reference's rule for integer literals,
      a suffix may begin with any letter other than @('e') and @('E'),
      and so with a letter that is a hexadecimal digit.
      So @('0x1f') can be read as a hexadecimal literal without a suffix,
      or as the hexadecimal literal @('0x1') with suffix @('f').
      The Reference's examples show the first reading
      (@('0x01_f32') is given as the integer 7986),
      and rustc does the same: the digits extend as far as they can.
      Our grammar has both readings, like the Reference;
      our lexer takes the digits as far as they go.
      For this reason, the side condition [SC7] tells
      whether a literal with a radix prefix has a suffix
      from its text, not from its CST
      (see @(tsee radix-literal-string-p))."))
   (xdoc::desc
    "A radix prefix read as the digit @('0') and the start of a suffix"
    (xdoc::p
     "Among its "
     (xdoc::ahref
      "https://doc.rust-lang.org/1.87.0/reference/tokens.html#reserved-forms-similar-to-number-literals"
      "reserved forms similar to number literals")
     ", which are rejected and not read as separate tokens,
      the Reference lists
      a radix prefix without digits (@('0b'), @('0b_')),
      a binary or octal literal followed by
      a decimal digit that is not of its radix (@('0b12')),
      and a binary or octal literal followed by @('e') or @('E')
      (@('0b1e')).
      But each of these texts also matches the rule for integer literals,
      as the decimal literal @('0') with a suffix
      (@('b'), @('b_'), @('b12'), @('b1e')).
      With more letters after it, that reading is even the longer one:
      in @('0b_a'), the reserved form is @('0b_'),
      and the integer literal with suffix @('b_a') is the whole text.
      A literal with a radix prefix has a second reading of this kind too,
      of the same length:
      @('0x3') matches as a hexadecimal literal,
      and also as the decimal literal @('0') with suffix @('x3').
      rustc never reads a radix prefix in that way:
      it rejects the reserved forms, also with more letters after them,
      and it reads @('0x3') as a hexadecimal literal.
      So do we, by the side condition [SC7]
      (see @(tsee lexeme-cst-reserved-number-okp))."))
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
    "A tuple index right after another"
    (xdoc::p
     "The Reference gives the "
     (xdoc::ahref
      "https://doc.rust-lang.org/1.87.0/reference/tokens.html#tuple-index"
      "tuple index")
     ", as in @('x.0'), as a rule of the lexer: it is an integer literal.
      But in @('x.0.1'), the text @('0.1') matches
      the Reference's rule for float literals,
      which gives the longer token,
      and the Reference does not say
      how the two tuple indices come out of it.
      rustc's lexer produces the float literal @('0.1') there,
      and rustc's parser splits it into the two indices.
      Our lexer produces the float literal as well;
      splitting it will be up to the parser."))
   (xdoc::h3 "In a later version of the Reference")
   (xdoc::p
    "After version 1.87.0, the Reference's lexical rules were rewritten
     as a grammar with ordered alternatives
     (see @(see related-lexer-descriptions)).
     In the version for Rust 1.100.0,
     the rules give what rustc does in all the cases above,
     with one exception.
     We have checked this by running, on inputs like the ones shown,
     the interpreter of the rules
     that comes with that version of the Reference,
     and rustc 1.100.0, which treats these inputs as rustc 1.87.0 does.
     The exception is @('/*') inside a block doc comment:
     those rules reject @('/* a /*/'), as rustc does,
     but they accept @('/*!/*/') and @('/** /*/'), which rustc rejects.")
   (xdoc::p
    "Two of the cases remain in the text of that version,
     though not in its rules.
     It still says that the zero width joiners
     are not allowed in identifiers,
     while its rules, like rustc, accept them.
     And it still gives the tuple index as a rule of the lexer,
     without saying how the two tuple indices of @('x.0.1')
     come out of the float literal that its rules,
     like rustc's lexer, produce there.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The topic below covers only the descriptions of Rust's lexical structure
; that are maintained and that help to check ours.
; A survey in November 2026 also found the work listed here,
; which we set aside for the reasons given;
; the list is here so that a later survey need not search for it again.
; A date is that of the last commit
; on the default branch of the repository.
;
; Unmaintained, or not precise about lexical structure:
;
; - rust-demo-semantics (K framework; fastxyz/rust-demo-semantics):
;   a partial grammar, whose tokens are regular expressions
;   with ASCII identifiers.  2024-11.
; - KRust (K framework; a paper of 2018):
;   a fragment of Rust, known to us from the paper only.
; - K-Rust and RustSEM (K framework; a paper of 2020):
;   a notation that is like Rust, not Rust's grammar.
; - ANTLR grammars-v4, directory rust:
;   its README says "Last updated for rust v1.60.0";
;   its predicates need code in the target language;
;   we found no comparison with rustc.
; - jorendorff/rust-grammar (ANTLR):
;   incomplete, by its own description.  2018-01.
; - The grammars that were in rustc's own repository, in src/grammar
;   (an ANTLR lexer grammar, with a program that
;   compared it with rustc's lexer; and a flex and bison grammar):
;   removed from the repository.
; - language-rust (Haskell, with Alex and Happy;
;   harpocrates/language-rust):
;   in its day it was compared with rustc.  2019-09.
; - rustypop (LALRPOP; nikomatsakis/rustypop):
;   never completed.  2017-02.
; - wg-grammar (rust-lang/wg-grammar): archived.  2024-04.
; - intellij-rust (its lexer and parser definitions):
;   the open repository ended when development moved
;   to the closed RustRover.  2024-01.
; - jinx-rust (TypeScript; jinxdash/jinx-rust):
;   tolerant of errors by design.  2022-09.
; - RustCompCert: a small unverified lexer for a subset of Rust.
;
; Maintained, but set aside for other reasons:
;
; - rust-analyzer: it uses rustc's own lexer
;   (the crate ra-ap-rustc_lexer), so it is not an independent check.
; - mrustc: an independent lexer, but one that assumes valid input,
;   and we found no way to make it print its tokens.
; - verusfmt (its grammar verus.pest) and lezer-parser/rust:
;   grammars made for tools; we found no comparison with rustc.
; - RustRover: closed source.
;
; Lexers that are independent of rustc but not checked against it,
; like those of gccrs and tree-sitter-rust,
; can supply test inputs, but they are not oracles.
; Neither is the crate proc-macro2:
; it accepts some suffixes and exponents that rustc's lexer rejects.

(defxdoc+ related-lexer-descriptions
  :parents (grammar)
  :short "Other descriptions of Rust's lexical structure,
          and how they relate to ours."
  :long
  (xdoc::topstring
   (xdoc::p
    "As far as we know, at this time of writing (November 2026),
     there is no other formalization of Rust's lexical structure,
     or of the rest of its concrete syntax, in a proof assistant:
     the verification tools for Rust that we know of
     start from the output of rustc's front end.
     The descriptions closest to ours are written
     for people to read and for testing, not for proofs;
     but they are precise, and two of them can be run.
     This topic says what they are,
     and where each has the counterpart of
     one of our side conditions
     (see @(see extra-grammatical-restrictions)).
     All of them describe later versions of Rust than 1.87.0,
     the version that our grammar follows (see @(see grammar)).")
   (xdoc::desc
    "lexeywan"
    (xdoc::p
     "This is a "
     (xdoc::ahref "https://github.com/mattheww/lexeywan"
                  "description of rustc's lexer")
     " by Matthew Woodcraft,
      for Rust 1.98 and the editions from 2015 to 2024.
      It has the same aim as our lexical grammar:
      to accept an input exactly if rustc's lexer does,
      which it takes to mean that rustc accepts the input
      as the input of a function-like macro.
      It is a parsing expression grammar:
      the alternatives of a rule are tried in order,
      a repetition takes all that it can,
      and an alternative may look ahead.
      Each match of a token rule then goes through a step,
      called processing, that may reject it;
      and some rules, called reserved forms,
      are there only for their matches to be rejected.
      It also describes what comes before the division into tokens
      (decoding the input,
      removing a byte order mark, a shebang line, and frontmatter,
      and normalizing line endings),
      and the turning of doc comments into attributes.
      Its tokens are finer than ours:
      every punctuation token is a single character,
      and keywords and the lone underscore
      are not told from identifiers.")
    (xdoc::p
     "It comes with an implementation of the description,
      and with a program that compares the implementation
      with rustc's lexer, called in the same process,
      and with what a macro receives from rustc,
      on about 1,500 inputs written by hand
      and on randomly generated ones.
      One of its checks goes over every Unicode character,
      to see that the two agree on whether
      the character may start, and may continue, an identifier.
      We have read it at its commit @('f118ae1'), of September 2026,
      to check our side conditions against its rules
      (see the table below);
      we have not run it."))
   (xdoc::desc
    "The Rust Reference, in later versions"
    (xdoc::p
     "Since its version for Rust 1.95.0, the "
     (xdoc::ahref
      "https://doc.rust-lang.org/1.100.0/reference/notation.html"
      "Reference")
     " says that the alternatives of its rules are tried in order,
      and its grammar has a cut operator:
      once the part of an alternative before the cut has matched,
      the rest of it must match, or the input is rejected.
      Since its version for Rust 1.96.0,
      the rules for number literals use cuts and lookaheads,
      where earlier versions had a list of reserved forms of numbers:
      for instance, a cut after @('0b') says that
      this text can only start a binary literal.
      And since its version for Rust 1.100.0,
      the Reference comes with an interpreter of its grammar,
      and with a tool that compares the tokens of the interpreter
      with those of rustc.
      So far only the lexical rules can be run.
      The grammar has no editions:
      its rules include the forms that only edition 2024 reserves.")
    (xdoc::p
     "We have run the interpreter of the version for Rust 1.100.0
      on about 188,000 short inputs,
      and compared it with rustc 1.100.0 in edition 2024,
      on whether each input lexes and into how many tokens.
      The two differ on one of those inputs, @('/*!/*/')
      (see @(see reference-vs-rustc)).
      We have also compared it with our lexer,
      on where each token starts and ends:
      the two agree on all those inputs,
      except on some with forms that our lexer does not cover yet
      (block doc comments, carriage returns in doc comments,
      and non-ASCII identifiers)."))
   (xdoc::desc
    "The Ferrocene Language Specification"
    (xdoc::p
     "The "
     (xdoc::ahref "https://rust-lang.github.io/fls/lexical-elements.html"
                  "FLS")
     " describes the lexical elements in prose,
      with syntax rules for each kind;
      it has no form that can be run.
      It follows the latest release of Rust,
      and its changelog lists, release by release,
      the changes to the language
      and the paragraphs that each change touches.
      That makes the changelog a list of
      what to look at when the version that we follow changes:
      for instance, it records under Rust 1.94.0
      rustc's move from Unicode 16 to Unicode 17,
      which changes the characters allowed in identifiers [SC4].
      Like the Reference, the FLS says that the zero width joiners
      must not appear in identifiers, while rustc accepts them
      (see @(see reference-vs-rustc))."))
   (xdoc::desc
    "A planned executable specification"
    (xdoc::p
     "One of the Rust project's goals for 2026 is an "
     (xdoc::ahref
      "https://rust-lang.github.io/rust-project-goals/2026/executable-spec.html"
      "executable specification")
     " of the whole language, from its surface syntax to its semantics,
      whose parser is to reuse the grammar of the Reference.
      When it covers lexing,
      it will be one more description to compare ours with."))
   (xdoc::h3 "Counterparts of our side conditions")
   (xdoc::p
    "This table gives, for each side condition of our lexical grammar,
     what plays its part in lexeywan (at the commit above)
     and in the Reference's version for Rust 1.100.0.
     The names are those of rules in the two grammars.")
   (xdoc::table_
    (xdoc::tr
     (xdoc::th "Ours")
     (xdoc::th "lexeywan")
     (xdoc::th "Reference 1.100.0"))
    (xdoc::tr
     (xdoc::td "[SC1] Maximal munch")
     (xdoc::td "The order of the alternatives;
                repetitions that take all they can.")
     (xdoc::td "The order of the alternatives;
                repetitions that take all they can;
                cuts."))
    (xdoc::tr
     (xdoc::td "[SC2] Block comment closing")
     (xdoc::td "The plain characters of @('BLOCK_COMMENT_CONTENT')
                exclude @('/*') as well as @('*/');
                @('Reserved_block_comment_start')
                rejects a comment that does not end.")
     (xdoc::td "The cut after @('/*') in @('BLOCK_COMMENT').
                There is none in @('NESTED_BLOCK_DOC_COMMENT'),
                which is why @('/*!/*/') is accepted."))
    (xdoc::tr
     (xdoc::td "[SC3] Carriage return in doc comments")
     (xdoc::td "Processing rejects a doc comment
                whose body has a carriage return.")
     (xdoc::td "@('LINE_DOC_COMMENT_CONTENT') and @('DOC_BLOCK_CHAR')
                exclude the carriage return."))
    (xdoc::tr
     (xdoc::td "[SC4] Unicode identifiers and their normalization")
     (xdoc::td "@('IDENT'), with the Unicode tables
                of the library that its implementation uses;
                the token holds the NFC form.")
     (xdoc::td "@('IDENTIFIER_OR_KEYWORD');
                the text names Unicode 17.0 and NFC."))
    (xdoc::tr
     (xdoc::td "[SC5] Raw identifier and raw lifetime exclusions")
     (xdoc::td "Processing rejects those matches of
                @('Raw_ident') and @('Raw_lifetime_or_label').")
     (xdoc::td "@('RESERVED_RAW_IDENTIFIER') and
                @('RESERVED_RAW_LIFETIME')."))
    (xdoc::tr
     (xdoc::td "[SC6] Keyword classification")
     (xdoc::td "None: keywords are not told from identifiers.")
     (xdoc::td "The lists of keywords,
                with the editions in the accompanying text."))
    (xdoc::tr
     (xdoc::td "[SC7] Reserved numeric forms")
     (xdoc::td "Processing rejects an @('Integer_literal')
                without digits, or with a digit that is not of its radix;
                @('Reserved_float') covers the forms with
                an exponent without digits, or with a radix prefix
                and an exponent or a period.")
     (xdoc::td "The cuts and lookaheads in @('BIN_LITERAL'),
                @('OCT_LITERAL'), and @('HEX_LITERAL');
                @('RESERVED_FLOAT');
                the cut in @('FLOAT_EXPONENT')."))
    (xdoc::tr
     (xdoc::td "[SC8] Reserved prefixes")
     (xdoc::td "@('Reserved_prefix_2021'), @('Reserved_literal_2021'),
                and @('Reserved_lifetime_or_label_prefix').")
     (xdoc::td "@('RESERVED_TOKEN_POUND'),
                @('RESERVED_TOKEN_DOUBLE_QUOTE'),
                @('RESERVED_TOKEN_SINGLE_QUOTE'),
                and @('RESERVED_TOKEN_LIFETIME')."))
    (xdoc::tr
     (xdoc::td "[SC9] Unicode escape values")
     (xdoc::td "Processing rejects a literal with a unicode escape
                whose value is not a Unicode scalar value,
                and a C string literal with a zero byte.")
     (xdoc::td "A condition in words on @('UNICODE_ESCAPE');
                a lookahead in the rule for C string literals
                excludes zero."))
    (xdoc::tr
     (xdoc::td "[SC10] Raw string termination")
     (xdoc::td "An extension of the grammar notation
                that remembers the @('#') characters matched
                (in @('RAW_DOUBLE_QUOTED_FORM'));
                @('HASHES') matches at most 255.")
     (xdoc::td "A counted repetition of @('#'), from 1 to 255 times,
                which must occur again after the closing quote
                (in @('RAW_STRING_LITERAL'))."))
    (xdoc::tr
     (xdoc::td "[SC11] Underscore after a character or string literal")
     (xdoc::td "Processing rejects a literal
                whose suffix is the single character @('_').")
     (xdoc::td "The cut in @('SUFFIX')."))
    (xdoc::tr
     (xdoc::td "[SC12] Single quote after a lifetime")
     (xdoc::td "@('Reserved_single_quoted_literal_2021').")
     (xdoc::td "The lookahead at the end of
                @('LIFETIME_TOKEN') and of @('RAW_LIFETIME')."))
    (xdoc::tr
     (xdoc::td "[SC13] String continuations")
     (xdoc::td "@('STRING_CONTINUATION_ESCAPE_BODY'),
                in its grammar of escapes.")
     (xdoc::td "@('STRING_CONTINUE')."))
    (xdoc::tr
     (xdoc::td "[SC14] Float literals ending with a period")
     (xdoc::td "The lookaheads after @('FLOAT_BODY_WITH_FINAL_DOT').")
     (xdoc::td "The lookahead in the last alternative of
                @('FLOAT_LITERAL').")))))
