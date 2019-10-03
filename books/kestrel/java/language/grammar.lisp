; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "kestrel/abnf/parser" :dir :system)
(include-book "kestrel/abnf/abstractor" :dir :system)

; (depends-on "lexical-grammar.txt")
; (depends-on "syntactic-grammar.txt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar
  :parents (language)
  :short "Grammar of the Java language [JLS]."
  :long
  (xdoc::topstring
   (xdoc::p
    "[JLS] presents the grammar of Java using the notation in [JLS:2.4],
     which is similar to EBNF (Extended Backus-Naur Form).
     But since we currently have a "
    (xdoc::seetopic "abnf::grammar-parser" "verified ABNF grammar parser")
    ", we use ABNF (Augmented Backus-Naur Form) to formalize the Java grammar.")
   (xdoc::p
    "The ABNF grammar of Java is in the files
     @('lexical-grammar.txt') and @('syntactic-grammar.txt')
     in this directory;
     this splitting corresponds to [JLS:2.2] and [JLS:2.3].
     Note that these files, according to ABNF,
     must have their lines terminated by carriage-return and line-feed pairs:
     see the notes "
    (xdoc::seetopic "abnf::parse-grammar-from-file" "here")
    " for details about this.")
   (xdoc::p
    "ABNF is a little different from EBNF.
     A difference is that EBNF has a construct for syntactic exception
     (e.g. @('consonant = letter - vowel')),
     while ABNF does not.
     The notation in [JLS:2.4]
     has a syntactic exception construct (@('but not'))
     that corresponds to EBNF's @('-') construct.
     However, the Java grammar alone is ambiguous anyhow,
     and we need extra-grammatical predicate to formalize Java syntax:
     we use those to formalize the syntactic exceptions in the Java grammar,
     since ABNF does not capture them.")
   (xdoc::p
    "While ABNF lacks syntactic exceptions,
     it has constructs that are not in EBNF or in the notation in [JLS:2.4],
     which actually allow us to capture more constraints in the grammar,
     or the same constraints slightly more concisely.
     In particular, ABNF has value range alternatives,
     which allow us to define @('RawInputCharacter') [JLS:3.3]
     without using informal prose.
     ABNF also has case-insensitive string terminal notations,
     which allow us to list the letters just once
     in the definition of @('HexDigit') [JLS:3.3].")
   (xdoc::p
    "The Java grammar in [JLS] uses camelcase nonterminals.
     Since rule names (i.e. nonterminals) are case-insensitive in ABNF,
     we systematically turn those camelcase nonterminals
     into dash-separated lowercase nonterminals.
     In the grammar files,
     we use ABNF comments for the @('but not') syntactic exceptions
     in the Java grammar in [JLS];
     this is just for documentation,
     because, as noted above, we formalize these syntactic exceptions
     via extra-grammatical predicates.
     We also use ABNF comments to separate the files into sections,
     and to reference the parts of [JLS] where the the rules appear.
     We use ABNF prose notation for certain nonterminals
     that are described in prose in [JLS].")
   (xdoc::p
    "The ABNF notation is documented in "
    (xdoc::a :href "https://www.rfc-editor.org/info/rfc5234" "RFC 5234")
    " and "
    (xdoc::a :href "https://www.rfc-editor.org/info/rfc7405" "RFC 7405")
    ". The correspondence with the notation in [JLS] should be clear."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection *lexical-grammar*
  :short "The Java lexical grammar, in ABNF."
  :long
  (xdoc::topstring-p
   "We parse the grammar file to obtain an ABNF grammar value.")
  (make-event
   (mv-let (tree state)
     (abnf::parse-grammar-from-file (str::cat (cbd) "lexical-grammar.txt")
                                    state)
     (value `(defconst *lexical-grammar*
               (abnf::abstract-rulelist ',tree))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection *syntactic-grammar*
  :short "The Java syntactic grammar, in ABNF."
  :long
  (xdoc::topstring-p
   "We parse the grammar file to obtain an ABNF grammar value.")
  (make-event
   (mv-let (tree state)
     (abnf::parse-grammar-from-file (str::cat (cbd) "syntactic-grammar.txt")
                                    state)
     (value `(defconst *syntactic-grammar*
               (abnf::abstract-rulelist ',tree))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *grammar*
  :short "The Java grammar, in ABNF."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put together lexical and syntactic grammar.
     The resulting grammar is well-formed and closed.")
   (xdoc::p
    "The goal symbol of the Java syntactic grammar is
     @('CompilationUnit') [JLS:2.3] [JLS:7.3].
     One might expect that the set of all strings derived from this goal symbol
     are a superset of all the syntactically valid Java programs
     (a superset because the grammar does not capture all the requirements).
     However, that is not quite the case, for the following reasons:")
   (xdoc::ul
    (xdoc::li
     "The syntactic grammar uses tokens as terminals [JLS:2.3].
      No white space and no comments can be derived from @('CompilationUnit').
      The lexical and syntactic grammars must be considered ``separately''
      in order to define
      (a superset of) the syntactically valid Java programs.")
    (xdoc::li
     "Considering the lexical grammar as a whole would imply that
      terminal symbols like the three forming the keyword @('for')
      have to be exactly those ASCII characters.
      However, [JLS:3.2] distinguishes three lexical translation steps,
      where the first one turns Unicode escapes into Unicode characters,
      which in particular turns Unicode escapes for ASCII characters
      into the corresponding ASCII characters.
      The OpenJDK 12 Java compiler indeed accepts @('\u0066\u006f\u0072')
      as the keyword @('for').
      Thus, the part of the lexical grammar
      that corresponds to this first lexical translation step
      must be considered separately from the rest."))
   (xdoc::p
    "The Java grammar is "
    (xdoc::seetopic "abnf::well-formedness" "well-formed")
    " and "
    (xdoc::seetopic "abnf::closure" "closed")
    "."))
  (append *lexical-grammar*
          *syntactic-grammar*)
  ///

  (defruled rulelist-wfp-of-*grammar*
    (abnf::rulelist-wfp *grammar*))

  (defruled rulelist-closedp-of-*grammar*
    (abnf::rulelist-closedp *grammar*)))
